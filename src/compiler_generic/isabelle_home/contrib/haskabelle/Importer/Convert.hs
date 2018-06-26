{-# LANGUAGE 
  MultiParamTypeClasses,
  FunctionalDependencies,
  FlexibleContexts,
  FlexibleInstances,
  TypeSynonymInstances,
  GeneralizedNewtypeDeriving,
  Rank2Types #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Conversion from abstract Haskell code to abstract Isar/HOL theory.
-}

module Importer.Convert (convertHskUnit, Conversion, runConversion, parseHskFiles, IsaUnit(..),
  liftIO, getOutputDir, getExportCode, getTryImport, getOnlyTypes, getBasePathAbs, getIgnoreNotInScope, getAbsMutParams, getCustomisations, getInputFilesRecursively) where

import Importer.Library
import qualified Importer.AList as AList
import qualified Data.Generics as G
import Data.Function
import Data.List (nub, unzip4, partition, isSuffixOf)
import Data.Maybe
import qualified Data.Set as Set hiding (Set)
import Data.Set (Set)
import qualified Data.Map as Map hiding (Map)
import Data.Map (Map)
import Data.Tree
import Data.Graph

import qualified Language.Preprocessor.Unlit as Unlit

import Control.Monad (foldM, mapAndUnzipM)
import Control.Monad.State (StateT, MonadState, get, put, modify, execStateT, runStateT)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (ReaderT, MonadReader, MonadIO, liftIO, ask, lift, runReaderT, local)
import Control.Monad.Writer (WriterT, MonadWriter, runWriterT, tell)

import System.FilePath
import System.Directory
import System.IO

import qualified Importer.Msg as Msg
import qualified Importer.Gensym as Gensym
import Importer.Configuration hiding (getMonadInstance, getCustomTheory)
import qualified Importer.Configuration as Config (getMonadInstance)
import qualified Importer.Configuration as Config (getCustomTheory)
import Importer.Adapt (makeAdaptionTable_FromHsModule, extractHskEntries,
  AdaptionTable, adaptGlobalEnv, adaptModules, Adaption(..))
import qualified Importer.Ident_Env as Ident_Env
import qualified Importer.Preprocess as Preprocess
import qualified Importer.DeclDependencyGraph as DeclDependencyGraph

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Hsx as Hsx
import qualified Importer.Isa as Isa


{-|
  This is the main function of the conversion process; converts a Unit of Haskell
  ASTs into a Unit of Isar/HOL ASTs.
-}
convertHskUnit :: Customisations -> Bool -> Bool -> Bool -> Adaption -> HskUnit -> (AdaptionTable, IsaUnit)
convertHskUnit custs exportCode ignoreNotInScope absMutParams adapt (HskUnit hsmodules custMods initialGlobalEnv)
    = let pragmass       = map (accumulate (fold add_pragmas) . snd) hsmodules
          hsmodules'     = map (Preprocess.preprocessModule (usedConstNames adapt) . Hsx.fmapUnit . fst) hsmodules
          env            = Ident_Env.environmentOf custs hsmodules' custMods
          adaptionTable  = makeAdaptionTable_FromHsModule adapt env hsmodules'
          initial_env    = Ident_Env.augmentGlobalEnv initialGlobalEnv $ extractHskEntries adaptionTable
          global_env_hsk = Ident_Env.unionGlobalEnvs env initial_env
                             
          hskmodules = map (toHskModule ignoreNotInScope global_env_hsk) $ Hsx.zipMod hsmodules'
          
          isathys = Isa.retopologizeModule $ fst $ runConversion' custs adapt global_env_hsk $
            mapM (convertModule exportCode absMutParams) (zip pragmass hskmodules)
          custThys = Map.elems custMods
          adaptedEnv = adaptGlobalEnv adaptionTable global_env_hsk
          isaunit = IsaUnit isathys custThys adaptedEnv
      in
        (adaptionTable, adaptIsaUnit adaptionTable global_env_hsk isaunit)
    where 
      toHskModule :: Bool -> Ident_Env.GlobalE -> (Hsx.ModuleName (), Hsx.Module ()) -> HskModule
      toHskModule ignoreNotInScope globalEnv (modul, Hsx.Module loc _ _ _ decls) =
        HskModule loc modul ((map HskDependentDecls . DeclDependencyGraph.arrangeDecls ignoreNotInScope globalEnv modul) decls)
      adaptIsaUnit adaptionTable globalEnv (IsaUnit modules custThys adaptedGlobalEnv) =
        IsaUnit (adaptModules adaptionTable adaptedGlobalEnv globalEnv modules) custThys adaptedGlobalEnv


type Pragma = (String, [String])

permissive_pragma = "permissive"

pragmas :: [String]
pragmas = [permissive_pragma]

add_pragmas :: Hsx.UnknownPragma -> [Pragma] -> [Pragma]
add_pragmas (Hsx.UnknownPragma src line) =
  case words line of
    "HASKABELLE" : pragma ->
      if null pragma then error ("empty pragma encountered at " ++ Hsx.srcspan2string src)
      else let
        directive : args = pragma
      in if directive `elem` pragmas
      then AList.map_default (directive, []) (fold insert args)
      else error ("unknown pragma " ++ directive ++ " encountered at " ++ Hsx.srcspan2string src)
    _ -> id


-- The naming scheme "HsFoo" is treated as being owned by the parser
-- libary Language.Haskell.Exts. We use "HskFoo" instead to
-- differentiate between what's defined by us and by that library. 
--
-- (Ok, this might sound somewhat confusing, at least we're consistent
-- about it.)

data HskModule = HskModule () (Hsx.ModuleName ()) [HskDependentDecls]
  deriving Show

{-|
  This data structure is supposed to collect function declarations
  that depend mutually recursive on each other.
-}
newtype HskDependentDecls = HskDependentDecls [Hsx.Decl ()]
  deriving Show

{-|
  ???
-}
data Context = Context {
  _theory :: Isa.ThyName,
  _globalEnv :: Ident_Env.GlobalE,
  _warnings :: [Warning],
  _backtrace :: [String],
  _adapt :: Adaption,
  _monad :: Maybe MonadInstance }

initContext adapt env = Context {
  _theory = Isa.ThyName "Scratch", {- FIXME: Default Hsx.ModuleName in Haskell
    is called `Main'; clashes with Isabelle. -}
  _globalEnv = env,
  _warnings = [],
  _backtrace = [],
  _adapt = adapt,
  _monad = Nothing }

{-|
  Instead of accessing a record directly by their `_foo' slots, we
  use the respective `foo' surrogate which consists of an appropriate
  getter and setter -- which allows functions to both query and
  update a record by slot name.
-}
type FieldSurrogate field = (Context -> field, Context -> field -> Context) 

theory :: FieldSurrogate Isa.ThyName
theory      = (_theory,      \c f -> c { _theory      = f })
globalEnv :: FieldSurrogate Ident_Env.GlobalE
globalEnv   = (_globalEnv,   \c f -> c { _globalEnv   = f })
warnings :: FieldSurrogate [Warning]
warnings    = (_warnings,    \c f -> c { _warnings    = f })
backtrace :: FieldSurrogate [String]
backtrace   = (_backtrace,   \c f -> c { _backtrace   = f })
adapt :: FieldSurrogate Adaption
adapt       = (_adapt,       \c f -> c { _adapt       = f })
monad     :: FieldSurrogate (Maybe MonadInstance)
monad       = (_monad,       \c f -> c { _monad       = f })

currentModule :: FieldSurrogate (Hsx.ModuleName ())
currentModule = (\c -> let (Isa.ThyName n) = _theory c in Hsx.ModuleName () n, \c f -> c)

getMonadInstance :: String -> ContextM (Maybe MonadInstance)
getMonadInstance name = ask >>= (return . flip Config.getMonadInstance name)

getMonadInstance' :: Hsx.Type () -> ContextM (Maybe MonadInstance)
getMonadInstance' ty =
    case Hsx.typeConName . Hsx.returnType $ ty of
      Nothing -> return Nothing
      Just name -> getMonadInstance name

withFunctionType :: Hsx.Type () -> ContextM a -> ContextM a
withFunctionType ty contextm = 
    do mbMon <- getMonadInstance' ty
       withUpdatedContext monad (const mbMon) contextm

withFunctionType' :: Maybe (Hsx.Type ()) -> ContextM a -> ContextM a
withFunctionType' mbTy contextm = 
    case mbTy of
      Nothing -> contextm
      Just ty -> withFunctionType ty contextm

withPossibleLift :: Hsx.Exp () -> ContextM a -> ContextM a
withPossibleLift name contextm = 
    do mbMon <- queryContext monad
       case mbMon of
         Nothing -> contextm
         Just mon -> 
             case varName name >>= getMonadLift mon of
               Nothing -> contextm
               newMon@(Just _) ->
                   withUpdatedContext monad (const newMon) contextm
    where uname (Hsx.Qual _ _ n) = n
          uname (Hsx.UnQual _ n) = n
          sname (Hsx.Ident _ n) = n
          sname (Hsx.Symbol _ n) = n
          qname (Hsx.Var _ n) = Just n
          qname _ = Nothing
          varName = liftM sname . liftM uname . qname

getCurrentMonadFunction :: Hsx.QName () -> ContextM (Hsx.QName ())
getCurrentMonadFunction name =
    do mbMon <- queryContext monad
       case mbMon of
         Nothing -> return name
         Just mon -> 
             case name of
               Hsx.Qual l mod uName -> return $ Hsx.Qual l mod (lookup mon uName)
               Hsx.UnQual l uName -> return $ Hsx.UnQual l (lookup mon uName)
               def -> return def
       where lookup mon (Hsx.Ident l name) = Hsx.Ident l $ getMonadConstant mon name
             lookup mon (Hsx.Symbol l name) = Hsx.Symbol l $ getMonadConstant mon name

getCurrentMonadDoSyntax :: ContextM (Maybe DoSyntax)
getCurrentMonadDoSyntax =
    do mbMon <- queryContext monad
       case mbMon of 
         Nothing -> return Nothing
         Just mon -> return . Just $ getMonadDoSyntax mon
         

{-|
  The conversion process is done in this monad.
-}
newtype ContextM v = ContextM (ReaderT Customisations (StateT Context Gensym.GensymM) v)
    deriving (Monad, MonadState Context, Functor, Applicative, MonadReader Customisations)

queryCustomisations = ask

{-|
  This function lifts a gensym computation to a context computation
-}
liftGensym :: Gensym.GensymM a -> ContextM a
liftGensym = ContextM . lift . lift

{-|
  This function executes the given conversion with the given environment as
  the context.
-}
runConversion' :: Customisations -> Adaption -> Ident_Env.GlobalE -> ContextM v -> (v, Context)
runConversion' custs adapt env (ContextM m) =
  Gensym.evalGensym Gensym.countInit $ runStateT (runReaderT m custs) (initContext adapt env)

{-|
  This function queries the given field in the context monad
-}
queryContext :: (FieldSurrogate field) -> ContextM field
queryContext (query, _)
    = do context <- get; return (query context) 

{-|
  This function updates the given field in the context monad using the given function.
-}
updateContext :: (FieldSurrogate field) -> (field -> field) -> ContextM ()
updateContext (query, update) updateField
    = do context <- get
         put (update context (updateField (query context)))
         return ()

{-|
  This function changes the given field in the given context monad using the given
  function. The original context is restored afterwards.
-}
withUpdatedContext :: (FieldSurrogate field) -> (field -> field) -> ContextM a -> ContextM a
withUpdatedContext surrogate updateField body
     = do oldval <- queryContext surrogate
          updateContext surrogate updateField
          result <- body
          updateContext surrogate (\_ -> oldval)
          return result

{-|
  This data structure is supposed to contain warning messages
-}
newtype Warning = Warning String
  deriving (Show, Eq, Ord)

{-|
  This function issues a warning in the current conversion monad.
-}
warn :: String -> ContextM ()
warn msg = updateContext warnings (\warnings -> warnings ++ [(Warning msg)])
     
{-|
  This function quits the conversion with an error providing the given error
  message.
-}
die :: String -> ContextM t
die msg 
    = do backtrace <- queryContext backtrace
         error $ msg ++ "\n\n"
                   ++ "Backtrace:\n"
                   ++ concat (map (++ "\n\n") (reverse backtrace))

{-|
  This function quits the conversion with an error providing the given error
  message and source location.
-}
dieWithLoc :: (){-Hsx.SrcLoc-} -> String -> ContextM t
dieWithLoc loc msg 
    = do backtrace <- queryContext backtrace
         error $ {-Hsx.srcloc2string loc ++ ": " ++-} msg ++ "\n\n"
                   ++ "Backtrace:\n"
                   ++ concat (map (++ "\n\n") (reverse backtrace))
{-|
  This function quits the conversion with an error that is due to a
  pattern matching case that was observed but not anticipated. The object
  causing this and an a string describing the context has to be provided.
-}
pattern_match_exhausted :: (Show a) => String -> a -> ContextM t
pattern_match_exhausted str obj 
    = die (str ++ ": Pattern match exhausted for\n" ++ Msg.prettyShow obj)


          
{-|
  This function generates the auxiliary functions for the given Haskell
  data type declaration. This includes accessor functions and update functions
-}
generateRecordAux :: [Pragma] -> Hsx.Decl () -> ContextM [Isa.Stmt]
generateRecordAux pragmas (Hsx.DataDecl _loc _kind _context _declhead condecls _deriving)
        = let strip (Hsx.QualConDecl _loc _FIXME _context decl) = decl
              decls = map strip condecls
              (tyconN, tyvarNs) = Hsx.split_declhead _declhead
          in do tyvars <- mapM (convert pragmas) tyvarNs
                let vs = map (rpair []) tyvars
                tycon <- convert pragmas tyconN
                let dataTy = Isa.Type tycon (map Isa.TVar tyvars)
                let fieldNames = concatMap extrFieldNames decls
                fields <- mapM (liftM fromJust . lookupIdentifier_Constant . Hsx.UnQual ()) (nub fieldNames)
                let funBinds = map (mkAFunBinds (length decls) vs dataTy) fields
                      ++ map (mkUFunBinds (length decls) vs dataTy) fields
                return funBinds
              where extrFieldNames (Hsx.RecDecl _ conName fields) = map fst $ Hsx.flattenRecFields fields
                    extrFieldNames _ = []
                    mkAFunBinds numCon vs dty (Ident_Env.Constant (Ident_Env.Field Ident_Env.LexInfo{Ident_Env.nameOf=fname, Ident_Env.typschemeOf=(_, fty)} constrs)) =
                        let binds = map (mkAFunBind fname) constrs
                            fname' = Isa.Name fname
                            funTy = Isa.Func dty (Ident_Env.toIsa fty)
                        in Isa.Function (Isa.Function_Stmt Isa.Primrec [Isa.TypeSign fname' vs funTy] binds)
                    mkAFunBind fname (Ident_Env.RecordConstr _ Ident_Env.LexInfo{Ident_Env.nameOf=cname} fields) =
                        let fname' = Isa.Name fname
                            con = Isa.Const $ Isa.Name cname
                            genArg (Ident_Env.RecordField n _)
                                | n == fname = Isa.Const (Isa.Name "x")
                                | otherwise = Isa.Const (Isa.Name "_")
                            conArgs = map genArg fields
                            pat = Isa.Parenthesized $ foldl Isa.App con conArgs
                            term = Isa.Const (Isa.Name "x")
                        in (fname', [pat], term)
                    mkUFunBinds numCon vs dty (Ident_Env.Constant (Ident_Env.Field Ident_Env.LexInfo{Ident_Env.nameOf=fname, Ident_Env.typschemeOf=(_, fty)} constrs)) =
                        let uname = "update_" ++ fname
                            binds = map (mkUFunBind fname uname) constrs
                            uname' = Isa.Name uname
                            funTy = Isa.Func (Ident_Env.toIsa fty) (Isa.Func dty dty)
                        in Isa.Function (Isa.Function_Stmt Isa.Primrec [Isa.TypeSign uname' vs funTy] binds)
                    mkUFunBind fname uname (Ident_Env.RecordConstr _ Ident_Env.LexInfo{Ident_Env.nameOf=cname} fields) =
                        let uname' = Isa.Name uname
                            con = Isa.Const $ Isa.Name cname
                            genPatArg (i,(Ident_Env.RecordField n _))
                                | n == fname = Isa.Const (Isa.Name "_")
                                | otherwise = Isa.Const (Isa.Name ("f" ++ show i))
                            genTermArg (i,(Ident_Env.RecordField n _))
                                | n == fname = Isa.Const (Isa.Name "x")
                                | otherwise = Isa.Const (Isa.Name ("f" ++ show i))
                            patArgs = map genPatArg (zip [1..] fields)
                            termArgs = map genTermArg (zip [1..] fields)
                            pat = Isa.Parenthesized $ foldl Isa.App con patArgs
                            term = Isa.Parenthesized $ foldl Isa.App con termArgs
                            arg = Isa.Const (Isa.Name "x")
                        in (uname', [arg,pat], term)


{-|
  This function converts a Haskell data type declaration into a
  Isabelle data type definition .
-}
convertDataDecl :: [Pragma] -> Hsx.Decl () -> ContextM (Isa.TypeSpec, [(Isa.Name, [Isa.Type])])
convertDataDecl pragmas (Hsx.DataDecl _loc _kind _context _declhead condecls _deriving)
    = let strip (Hsx.QualConDecl _loc _FIXME _context decl) = decl
          decls = map strip condecls
          (tyconN, tyvarNs) = Hsx.split_declhead _declhead
      in do tyvars <- mapM (convert pragmas) tyvarNs
            tycon  <- convert pragmas tyconN
            decls' <- mapM cnvt decls
            return $ (Isa.TypeSpec tyvars tycon, decls')
              where cnvt (Hsx.ConDecl _ name types)
                        = do name'  <- convert pragmas name
                             tyvars <- mapM (convert pragmas) types
                             return $ (name', tyvars)
                    cnvt (Hsx.RecDecl _ name fields) = 
                        let types = map snd (Hsx.flattenRecFields fields)
                        in do name'  <- convert pragmas name
                              tyvars <- mapM (convert pragmas) types
                              return $ (name', tyvars)

{-|
  Instances of this class constitute pairs of types s.t. the first one
  (a Haskell entity) can be converted into the last one (an Isabelle entity).
  
  Instance declarations are supposed to implement 'convert'' instead of 
  'convert'. The latter uses the first by adding further boilerplate code.
-}
class Show a => Convert a b | a -> b where
    convert' :: [Pragma] -> Convert a b => a -> ContextM b
    convert  :: [Pragma] -> Convert a b => a -> ContextM b
    convert pragmas hsexpr = withUpdatedContext backtrace 
                       (\bt -> let frameName = "frame" ++ show (length bt)
                               in Msg.prettyShow' frameName hsexpr : bt)
                     $ convert' pragmas hsexpr

convertModule :: Bool -> Bool -> ([Pragma], HskModule) -> ContextM Isa.Module
convertModule exportCode absMutParams (pragmas, HskModule _loc modul dependentDecls) =
  do
    thy <- convert pragmas modul
    env <- queryContext globalEnv
    adaption <- queryContext adapt
    custs <- queryCustomisations
    let imps = filter (not . isStandardTheory (usedThyNames adaption)) (lookupImports thy env custs)
    withUpdatedContext theory (\t -> assert (t == Isa.ThyName "Scratch") thy)
      $ do
          stmts <- mapsM (convertDependentDecls absMutParams pragmas) dependentDecls
          return (Isa.retopologize (Isa.Module thy imps stmts exportCode))
  where isStandardTheory usedThyNames (Isa.ThyName n) = n `elem` usedThyNames

lookupImports :: Isa.ThyName -> Ident_Env.GlobalE -> Customisations -> [Isa.ThyName]
lookupImports thy globalEnv custs
    = map (rename .(\(Ident_Env.Import name _ _) ->  Ident_Env.toIsa name))
        $ Ident_Env.lookupImports (Ident_Env.fromIsa thy) globalEnv
    where rename orig@(Isa.ThyName name) = case Config.getCustomTheory custs (Hsx.ModuleName () name) of
                                   Nothing -> orig
                                   Just ct -> getCustomTheoryName ct

convertDependentDecls :: Bool -> [Pragma] -> HskDependentDecls -> ContextM [Isa.Stmt]
convertDependentDecls _ pragmas (HskDependentDecls [])  =
  return []
convertDependentDecls _ pragmas (HskDependentDecls [d]) = do
  d <- convertDecl pragmas d
  return d
convertDependentDecls absMutParams pragmas (HskDependentDecls decls@(decl:_))
  | isFunBind decl = assert (all isFunBind decls)
      $ do funcmds <- mapsM (convertDecl pragmas) decls
           let (kinds, sigs, eqs) = unzip3 (map splitFunCmd funcmds)
           let kind = if any (== Isa.Function_Sorry) kinds then Isa.Function_Sorry else Isa.Fun
           return [Isa.Function (Isa.Function_Stmt kind sigs (flat eqs))]
  | otherwise = 
        let (decls', tydecls) = partition isDataDecl decls
            decls'' = G.everywhere (G.mkT $ replaceTy (map (\t -> case t of Hsx.TypeDecl _ (Hsx.DHead _ i) ty -> ((i, Nothing), ty)
                                                                            Hsx.TypeDecl _ (Hsx.DHApp _ (Hsx.DHead _ i) (Hsx.UnkindedVar _ i')) ty -> ((i, Just i'), ty)) tydecls)) decls' in
        do
           dataDefs <- mapM (convertDataDecl pragmas) decls''
           params' <- foldM (\res (Isa.TypeSpec params _, _) ->
                              if all (uncurry (==)) (zip res params) then
                                return $ if length res > length params then res else params
                              else
                                error Msg.unsupported_semantics_decl)
                            []
                            dataDefs
           auxCmds <- mapM (generateRecordAux pragmas) decls''
           tyDefs <- mapM (\x -> convertDependentDecls absMutParams pragmas $ HskDependentDecls [x]) tydecls
           return (Isa.Datatype (map (let names = dataDefs
                                                & map (\(Isa.TypeSpec _ name, _) -> name)
                                                & Set.fromList in
                                      \(tySpec, ty) -> ( replaceParamsTySpec params' names tySpec
                                                       , G.everywhere' (G.mkT $ replaceParamsTy (map Isa.TVar params') names) ty)) dataDefs)
                   : concat (auxCmds ++ tyDefs))
  where 
    isFunBind (Hsx.FunBind _ _) = True
    isFunBind _ = False
    isDataDecl (Hsx.DataDecl _ _ _ _ _ _) = True
    isDataDecl _ = False
    splitFunCmd (Isa.Function (Isa.Function_Stmt kind [sig] eqs)) = (kind, sig, eqs)
    replaceTy :: [((Hsx.Name (), Maybe (Hsx.Name ())), Hsx.Type ())] -> Hsx.Type () -> Hsx.Type ()
    replaceTy tydecls t = case t of Hsx.TyCon _ (Hsx.UnQual _ i) -> maybe t id $ AList.lookup tydecls (i, Nothing)
                                    Hsx.TyApp _ (Hsx.TyCon _ (Hsx.UnQual _ i)) (Hsx.TyVar _ i') -> maybe t id $ AList.lookup tydecls (i, Just i')
                                    _ -> G.gmapT (G.mkT $ replaceTy tydecls) t
    replaceParamsTySpec :: [Isa.Name] -> Set Isa.Name -> Isa.TypeSpec -> Isa.TypeSpec
    replaceParamsTySpec params set t@(Isa.TypeSpec _ name) = if Set.member name set then Isa.TypeSpec params name else t
    replaceParamsTy :: [Isa.Type] -> Set Isa.Name -> Isa.Type -> Isa.Type
    replaceParamsTy params set (Isa.Type name t') = replaceParamsTy' (if absMutParams then params else t' ++ foldl (\params _ -> tail params) params t') set name (Isa.Type name (map (replaceParamsTy params set) t'))
    replaceParamsTy params set (Isa.Func t1 t2)   = Isa.Func (replaceParamsTy params set t1) (replaceParamsTy params set t2)
    replaceParamsTy params set t@(Isa.TVar name)  = replaceParamsTy' params set name t
    replaceParamsTy params set Isa.NoType         = Isa.NoType
    replaceParamsTy' params set name t = if Set.member name set then Isa.Type name params else t


instance Convert (Hsx.Module ()) Isa.Stmt where
    convert' pragmas (Hsx.Module loc _ _ _ _)
        = dieWithLoc loc "Internal Error: Each Hsx.Module should have been pre-converted to HskModule."


--- Trivially convertable stuff.

instance Convert (Hsx.ModuleName ()) Isa.ThyName where
    convert' pragmas m = return (Ident_Env.toIsa (Ident_Env.fromHsk m :: Ident_Env.ModuleID))

instance Convert (Hsx.Name ()) Isa.Name where
    convert' pragmas n = return (Ident_Env.toIsa (Ident_Env.fromHsk n :: Ident_Env.Name))

instance Convert (Hsx.QName ()) Isa.Name where
    convert' pragmas qn = return (Ident_Env.toIsa (Ident_Env.fromHsk qn :: Ident_Env.Name))

instance Convert (Hsx.Type ()) Isa.Type where
    convert' pragmas t @ (Hsx.TyForall _ _ _ _) = pattern_match_exhausted "Hsx.Type () -> Isa.Type" t
    convert' pragmas t = return (Ident_Env.toIsa (Ident_Env.fromHsk t :: Ident_Env.Type))

instance Convert (Hsx.TyVarBind ()) Isa.Name where
    convert' pragmas (Hsx.KindedVar _ n _) = convert' pragmas n
    convert' pragmas (Hsx.UnkindedVar _ n) = convert' pragmas n

convert_type_sign :: Hsx.Name () -> Hsx.Type () -> Isa.TypeSign
convert_type_sign n typ =
  let
    n' = Ident_Env.toIsa (Ident_Env.fromHsk n :: Ident_Env.Name)
    (e_vs, e_typ) = Ident_Env.typscheme_of_hsk_typ typ
    vs' = map (\(v, sort) -> (Ident_Env.toIsa v, Ident_Env.isa_of_sort sort)) e_vs
    typ' = Ident_Env.toIsa e_typ
  in Isa.TypeSign n' vs' typ'

instance Convert (Hsx.QOp ()) Isa.Term where
    convert' pragmas (Hsx.QVarOp _ qname) = do qname' <- convert pragmas qname; return (Isa.Const qname')
    convert' pragmas (Hsx.QConOp _ qname) = do qname' <- convert pragmas qname; return (Isa.Const qname')
    -- convert' junk = pattern_match_exhausted "Hsx.QOp () -> Isa.Term" junk

instance Convert (Hsx.Op ()) Isa.Name where
    convert' pragmas (Hsx.VarOp _ qname) = convert pragmas qname
    convert' pragmas (Hsx.ConOp _ qname) = convert pragmas qname
    -- convert' junk = pattern_match_exhausted "HsOp -> Isa.Name" junk

instance Convert (Hsx.Literal ()) Isa.Literal where
    convert' pragmas (Hsx.Int _ i _)      = return (Isa.Int i)
    convert' pragmas (Hsx.Char _ ch _)    = return (Isa.Char ch)
    convert' pragmas (Hsx.String _ str _) = return (Isa.String str)
    convert' pragmas junk           = pattern_match_exhausted "HsLiteral -> Isa.Literal" junk


--- Not so trivially convertable stuff.

convertDecl :: [Pragma] -> Hsx.Decl () -> ContextM [Isa.Stmt]
convertDecl pragmas (Hsx.TypeDecl _loc _declhead typ)
        = let (tyconN, tyvarNs) = Hsx.split_declhead _declhead in
          do tyvars <- mapM (convert pragmas) tyvarNs
             tycon  <- convert pragmas tyconN
             typ'   <- convert pragmas typ
             return [Isa.TypeSynonym [(Isa.TypeSpec tyvars tycon, typ')]]
                                
convertDecl pragmas decl@(Hsx.DataDecl _ _ _ _ _ _) = 
        do dataDef <- convertDataDecl pragmas decl
           accCmds <- generateRecordAux pragmas decl
           return (Isa.Datatype [dataDef] : accCmds)

convertDecl pragmas (Hsx.InfixDecl _loc assoc prio ops)
        = do (assocs, prios) <- mapAndUnzipM (lookupInfixOp . toQOp) ops 
             assert (all (== assoc) assocs && all (== prio) prios) 
               $ return []
        where toQOp (Hsx.VarOp _ n) = Hsx.QVarOp () (Hsx.UnQual () n)
              toQOp (Hsx.ConOp _ n) = Hsx.QConOp () (Hsx.UnQual () n)

convertDecl pragmas (Hsx.TypeSig _loc names typ)
        = do globalEnv <- queryContext globalEnv
             modul     <- queryContext currentModule
             types     <- liftM catMaybes $ mapM (lookupType . Hsx.UnQual ()) names
             assert (all (== typ) types) 
               $ return []
                         
    -- Remember that at this stage there are _no_ local declarations in the Hsx
    -- AST anymore, as we made those global during the preprocessing stage.
    -- 
    --   E.g.                                                       fun g0 :: "Int => Int"    
    --                                    g0 :: Int -> Int          where                      
    --    f :: Int -> Int                 g0 0 = 0                    "g0 0 = 0"              
    --    f x = g x                       g0 n = n + g0 (n-1)       | "g0 n = n + g0 (n - 1)"
    --      where g :: Int -> Int   ==>                        ==>                            
    --            g 0 = 0                 f :: Int -> Int           fun f :: "Int => Int"     
    --            g n = n + g (n-1)       f x = g0 x                where                     
    --                                                                "f x = g0 x"            
    --
convertDecl pragmas (Hsx.FunBind _ matchs)
        = do let (names, patterns, bodies, wbinds) = unzip4 (map splitMatch matchs)
             assert (all (== head names) (tail names)) (return ())
             assert (all Preprocess.isEmptyBinds wbinds) (return ()) -- all decls are global at this point.
             ftype <- lookupType (Hsx.UnQual () (names !! 0)) -- as all names are equal, pick first one.
             let name = names !! 0
             name' <- convert' pragmas name
             let n = name_of name
             let kind = if n `elem` these (lookup permissive_pragma pragmas)
                  then Isa.Function_Sorry else Isa.Fun
             let fsig' = case ftype of { 
               Nothing -> Isa.TypeSign name' [] Isa.NoType;
               Just typ -> convert_type_sign name typ }
             patsNames  <- mapM (mapM (convert pragmas)) patterns
             let patsNames' = map unzip patsNames
                 patterns'  = map fst patsNames'
                 aliases    = map (concat.snd) patsNames'
             bodies'    <- withFunctionType' ftype $
                                mapM (convert pragmas) bodies
             let bodies'' = zipWith mkSimpleLet aliases bodies'
             thy        <- queryContext theory
             return [Isa.Function (Isa.Function_Stmt kind [fsig']
               (zip3 (repeat (Isa.name_of_type_sign fsig')) patterns' bodies''))]
       where splitMatch (Hsx.Match _loc name patterns (Hsx.UnGuardedRhs _ body) wherebind)
                 = (name, patterns, body, wherebind)
             splitMatch (Hsx.InfixMatch _loc pattern name patterns (Hsx.UnGuardedRhs _ body) wherebind)
                 = (name, pattern : patterns, body, wherebind)
             name_of (Hsx.Ident _ n) = n
             name_of _ = ""

convertDecl pragmas (Hsx.PatBind loc pattern rhs _wherebinds)
        = case pattern of
            pat@(Hsx.PVar _ name) 
                -> do name' <- convert pragmas name
                      (pat', aliases)  <- convert pragmas pat
                      rhs'  <- convert pragmas rhs
                      let rhs'' = mkSimpleLet aliases rhs'
                      ftype <- lookupType (Hsx.UnQual () name)
                      let sig' = case ftype of { 
                        Nothing -> Isa.TypeSign name' [] Isa.NoType;
                        Just typ -> convert_type_sign name typ }
                      return [Isa.Function (Isa.Function_Stmt Isa.Definition [sig'] [(name', [], rhs'')])]
            _   -> dieWithLoc loc (Msg.complex_toplevel_patbinding)
    
convertDecl pragmas decl@(Hsx.ClassDecl _ ctx declhead _ class_decls)
        = check_class_decl decl
            $ do let (classN, _) = Hsx.split_declhead declhead
                 let superclassNs   = Hsx.extractSuperclassNs ctx
                 superclassNs' <- mapM (convert pragmas) superclassNs
                 classN'       <- convert pragmas classN
                 typesigs'     <- mapsM convertToTypeSig $ class_decls_list class_decls
                 return [Isa.Class classN' superclassNs' typesigs']
        where
          class_decls_list Nothing = []
          class_decls_list (Just l) = l
          check_class_decl (Hsx.ClassDecl loc ctx declhead fundeps decls) cont
              | length (snd $ Hsx.split_declhead declhead) /= 1  = dieWithLoc loc (Msg.only_one_tyvar_in_class_decl)
              | not (null fundeps)                               = dieWithLoc loc (Msg.no_fundeps_in_class_decl)
              | not (all isTypeSig $ class_decls_list decls)     = dieWithLoc loc (Msg.no_default_methods_in_class_decl)
              | otherwise                                        = cont
          isTypeSig decl = case decl of 
                             Hsx.ClsDecl _ (Hsx.TypeSig _ _ _) -> True
                             _                                 -> False
          convertToTypeSig (Hsx.ClsDecl _ (Hsx.TypeSig _ names typ))
                  = do names' <- mapM (convert pragmas) names
                       typ'   <- convert pragmas typ {-FIXME-}
                       return (map (\name' -> Isa.TypeSign name' [] typ') names')

convertDecl pragmas (Hsx.InstDecl loc _ instrule (Just stmts)) =
  case get_instrule instrule of
    (_, ctx, insthead) ->
      case Hsx.split_insthead insthead of
        (cls, [typ]) ->
          do
            cls' <- convert pragmas cls
            typ' <- convert pragmas typ
            case dest_typ_tvars typ' of
              Nothing -> dieWithLoc loc Msg.only_simple_instantiations
              Just (tyco', vs') -> do
                raw_arities <- mapM (convert_arity) (case ctx of Nothing -> [] ; Just ctx -> Hsx.dest_typcontext ctx)
                let arities' = AList.make (the . AList.lookup raw_arities) vs';
                identifier <- lookupIdentifier_Type cls
                let classinfo = case fromJust identifier of
                                      Ident_Env.TypeDecl (Ident_Env.Class _ classinfo) -> classinfo
                                      t -> error $ "found:\n" ++ show t
                let methods = Ident_Env.methodsOf classinfo
                let classVarN = Ident_Env.classVarOf classinfo
                let inst_envtype = Ident_Env.fromHsk typ
                let tyannots = map (mk_method_annotation classVarN inst_envtype) methods
                withUpdatedContext globalEnv (\e -> Ident_Env.augmentGlobalEnv e tyannots) $
                  do stmts' <- mapsM (convertDecl pragmas) (map toHsDecl stmts)
                     let fun_stmts' = map (\(Isa.Function fun_stmt) -> fun_stmt) stmts'
                     return [Isa.Instance cls' tyco' arities' fun_stmts']
          where
            dest_typ_tvars (Isa.Type tyco typs) = case perhaps_map dest_tvar typs of
              Nothing -> Nothing
              Just vs -> Just (tyco, vs)
            dest_typ_tvars _ = Nothing
            dest_tvar (Isa.TVar v) = Just v
            dest_tvar _ = Nothing
            convert_arity (v, sort) = do
              v' <- convert pragmas v
              sort' <- mapM (convert pragmas) sort
              return (v', sort')
            toHsDecl (Hsx.InsDecl _ decl) = decl
            mk_method_annotation :: Ident_Env.Name -> Ident_Env.Type -> Ident_Env.Identifier -> Ident_Env.Identifier
            mk_method_annotation tyvarN tycon class_method_annot
                = assert (Ident_Env.isTypeAnnotation class_method_annot)
                    $ let lexinfo = Ident_Env.lexInfoOf class_method_annot
                          (_, typ)     = Ident_Env.typschemeOf lexinfo
                          typ'    = Ident_Env.substituteTyVars [(Ident_Env.TyVar tyvarN, tycon)] typ
                      in Ident_Env.Constant (Ident_Env.TypeAnnotation (lexinfo { Ident_Env.typschemeOf = ([], typ') }))
        _ -> dieWithLoc loc (Msg.only_one_tyvar_in_class_decl)


convertDecl pragmas junk = pattern_match_exhausted "Hsx.Decl () -> Isa.Stmt" junk


get_instrule (Hsx.IRule _ t c h) = (t, c, h)
get_instrule (Hsx.IParen _ r) = get_instrule r

instance Convert (Hsx.Binds ()) [Isa.Stmt] where
    convert' pragmas (Hsx.BDecls _ decls) = mapsM (convertDecl pragmas) decls
    convert' pragmas junk = pattern_match_exhausted "Hsx.Binds () -> Isa.Stmt" junk

mkList :: [Isa.Term] -> Isa.Term
mkList = foldr
         (\x xs -> Isa.App (Isa.App (Isa.Const (Isa.Name "List.Cons")) x) xs)
         (Isa.Const (Isa.Name "List.Nil"))

mkSimpleLet :: [(Isa.Name, Isa.Term)] -> Isa.Term -> Isa.Term
mkSimpleLet [] body = body
mkSimpleLet binds body = Isa.Let binds' body
    where binds' = map (\(a,b) -> (Isa.Const a, b)) binds

type PatternE = Bool
type PatternO = [(Isa.Name,Isa.Term)]

newtype PatternM a = PatternM ((ReaderT PatternE (WriterT PatternO ContextM)) a)
    deriving (Monad, MonadReader PatternE, MonadWriter PatternO, Functor, Applicative)

runPatternM :: PatternM a -> ContextM (a,PatternO)
runPatternM (PatternM pm) =  (runWriterT (runReaderT pm False))

liftConvert :: ContextM a -> PatternM a
liftConvert = PatternM . lift . lift

withAsPattern :: PatternM a -> PatternM a
withAsPattern = local (const True)

isInsideAsPattern :: PatternM Bool
isInsideAsPattern = ask

addAlias :: (Isa.Name, Isa.Term) -> PatternM ()
addAlias = tell . (:[])

convertPat :: [Pragma] -> Hsx.Pat () -> PatternM Isa.Pat
convertPat pragmas (Hsx.PVar _ name) = 
    do name' <- liftConvert $ convert pragmas name
       return (Isa.Const name')
convertPat pragmas (Hsx.PLit _ (Hsx.Signless _) lit) = 
    do lit' <- liftConvert $ convert pragmas lit
       return (Isa.Literal lit')
              
convertPat pragmas infixapp@Hsx.PInfixApp{} = 
    do (Hsx.PInfixApp _ p1 qname p2) <- liftConvert $ fixOperatorFixities' infixapp
       p1' <- convertPat pragmas p1 
       qname'   <- liftConvert $ convert pragmas qname
       p2' <- convertPat pragmas p2
       return (Isa.App (Isa.App (Isa.Const qname') p1') p2')

convertPat pragmas (Hsx.PApp _ qname pats) = 
    do qname' <- liftConvert $ convert pragmas qname
       pats' <- mapM (convertPat pragmas) pats
       return $ foldl Isa.App (Isa.Const qname') pats'
       
convertPat pragmas (Hsx.PTuple _ Hsx.Boxed comps) = 
    convertPat pragmas (foldr Hsx.hskPPair (Hsx.PParen () (last comps)) (init comps))

convertPat pragmas (Hsx.PList _ []) =
    do list_datacon_name <- liftConvert $ convert pragmas (Hsx.Special () (Hsx.ListCon ()))
       return (Isa.Const list_datacon_name)

convertPat pragmas (Hsx.PList _ els) =
    convertPat pragmas $ foldr Hsx.hskPCons Hsx.hskPNil els

convertPat pragmas (Hsx.PParen _ pat) = 
    do pat' <- convertPat pragmas pat
       return (Isa.Parenthesized pat')

convertPat pragmas (Hsx.PRec _ qname fields) = 
    do mbConstr <- liftConvert $ lookupIdentifier_Constant qname
       case mbConstr of
         Just (Ident_Env.Constant (Ident_Env.Constructor (Ident_Env.RecordConstr _ _ recFields))) -> 
             do isAs <- isInsideAsPattern
                let fields' = map (\(Hsx.PFieldPat _ name pat) -> (Ident_Env.fromHsk name, pat)) fields
                    toSimplePat (Ident_Env.RecordField iden _) = 
                        case lookup iden fields' of
                          Nothing -> if isAs
                                     then liftConvert . liftGensym . liftM Isa.Const . liftM Isa.Name $
                                          Gensym.gensym "a"
                                     else return (Isa.Const (Isa.Name "_"))
                          Just pat -> convertPat pragmas pat
                recArgs <- mapM toSimplePat recFields
                qname' <- liftConvert $ convert pragmas qname
                return $ Isa.Parenthesized (foldl Isa.App (Isa.Const qname') recArgs)
         _ -> liftConvert . die $ "Record constructor " ++ Msg.quote qname ++ " is not declared in environment!"

convertPat pragmas (Hsx.PAsPat _ name pat) = 
    do name' <- liftConvert $ convert pragmas name
       pat' <- withAsPattern $ convertPat pragmas pat
       addAlias (name', pat')
       return pat'
convertPat pragmas (Hsx.PWildCard _) = 
    do isAs <- isInsideAsPattern
       if isAs
         then liftConvert . liftGensym . liftM Isa.Const . liftM Isa.Name $
              Gensym.gensym "a"
         else return (Isa.Const (Isa.Name "_"))

convertPat pragmas junk = liftConvert $ pattern_match_exhausted 
                  "Hsx.Pat () -> Isa.Term" 
                  junk
instance Convert (Hsx.Pat ()) (Isa.Pat, [(Isa.Name, Isa.Term)]) where
    convert' pragmas  = runPatternM . convertPat pragmas 

instance Convert (Hsx.Rhs ()) Isa.Term where
    convert' pragmas (Hsx.UnGuardedRhs _ exp) = convert pragmas exp
    -- convert (Hsx.GuardedRhss rhss) ; FIXME
    convert' pragmas junk = pattern_match_exhausted "Hsx.Rhs () -> Isa.Term" junk

instance Convert (Hsx.FieldUpdate ()) (Isa.Name, Isa.Term) where
    convert' pragmas (Hsx.FieldUpdate _ qname exp)
        = do qname' <- convert pragmas qname
             exp'   <- convert pragmas exp
             return (qname', exp')

instance Convert (Hsx.Alt ()) (Isa.Term, Isa.Term) where
    convert' pragmas (Hsx.Alt _loc pat (Hsx.UnGuardedRhs _ exp) _wherebinds)
        = do (pat',aliases) <- convert pragmas pat
             exp' <- convert pragmas exp
             let exp'' = mkSimpleLet aliases exp'
             return (pat', exp'')
    convert' pragmas junk 
        = pattern_match_exhausted "Hsx.Alt () -> (Isa.Term, Isa.Term)" junk


instance Convert (Hsx.Exp ()) Isa.Term where
    convert' pragmas (Hsx.Lit _ lit)       = convert pragmas lit   >>= (\l -> return (Isa.Literal l))
    convert' pragmas (Hsx.Var _ qname)     =
        do qname' <- getCurrentMonadFunction qname
           convert pragmas qname' >>= (\n -> return (Isa.Const n))
    convert' pragmas (Hsx.Con _ qname)     = convert pragmas qname >>= (\n -> return (Isa.Const n))
    convert' pragmas (Hsx.Paren _ exp)     = convert pragmas exp   >>= (\e -> return (Isa.Parenthesized e))
    -- convert' (Hsx.WildCard _)      = return (Isa.Const (Isa.Name "_"))
    convert' pragmas (Hsx.NegApp _ exp)    = convert pragmas (Hsx.hsk_negate exp)

    convert' pragmas (Hsx.List _ [])       = do
      list_datacon_name <- convert pragmas (Hsx.Special () (Hsx.ListCon ()))
      return (Isa.Const list_datacon_name)
    convert' pragmas (Hsx.List _ exps)
        = convert pragmas $ foldr Hsx.hsk_cons Hsx.hsk_nil exps

    -- We have to wrap the last expression in an explicit HsParen as that last
    -- expression may itself be a pair. If we didn't, we couldn't distinguish
    -- between "((1,2), (3,4))" and "((1,2), 3, 4)" afterwards anymore.
    convert' pragmas (Hsx.Tuple _ Hsx.Boxed exps) = convert pragmas (foldr Hsx.hsk_pair (Hsx.Paren () (last exps)) (init exps))

    convert' pragmas (Hsx.App _ exp1 exp2)
        = do exp1' <- convert pragmas exp1
             exp2' <- withPossibleLift exp1 $ convert pragmas exp2
             return (Isa.App exp1' exp2')

    convert' pragmas infixapp@(Hsx.InfixApp _ _ _ _)
        = do (Hsx.InfixApp _ exp1 op exp2) <- fixOperatorFixities infixapp
             exp1' <- convert pragmas exp1 
             op'   <- convert pragmas op
             exp2' <- if isApp op
                       then withPossibleLift exp1 $ convert pragmas exp2
                       else convert pragmas exp2
             return (mkInfixApp exp1' op' exp2')
        where 
          uname (Hsx.Qual _ _ n) = n
          uname (Hsx.UnQual _ n) = n
          isApp (Hsx.QVarOp _ qname) =
              case uname qname of
                Hsx.Ident _ _ -> False
                Hsx.Symbol _ sym -> sym == "$"
          isApp _ = False
          mkInfixApp t1 op t2 = Isa.App (Isa.App op t1) t2

    convert' pragmas (Hsx.LeftSection _ e qop)
        = do e'   <- convert pragmas e
             qop' <- convert pragmas qop
             g    <- liftGensym (Gensym.genIsaName (Isa.Name "arg"))
             return (makeAbs [g] $ Isa.App (Isa.App qop' e') (Isa.Const g))

    convert' pragmas (Hsx.RightSection _ qop e)
        = do e'   <- convert pragmas e
             qop' <- convert pragmas qop
             g <- liftGensym (Gensym.genIsaName (Isa.Name "arg"))
             return (makeAbs [g] $ Isa.App (Isa.App qop' (Isa.Const g)) e')

    convert' pragmas (Hsx.RecConstr _ qname updates) = 
        do mbConstr <- lookupIdentifier_Constant qname
           case mbConstr of
             Just (Ident_Env.Constant (Ident_Env.Constructor (Ident_Env.RecordConstr _ _ recFields))) -> 
                 let updates' = map (\(Hsx.FieldUpdate _ name exp) -> (Ident_Env.fromHsk name, exp)) updates
                     toSimplePat (Ident_Env.RecordField iden _) = 
                         case lookup iden updates' of
                           Nothing -> Hsx.Var () (Hsx.UnQual () (Hsx.Ident () "undefined"))
                           Just exp -> exp
                     recArgs = map toSimplePat recFields
                 in convert' pragmas $ foldl (Hsx.App ()) (Hsx.Con () qname) recArgs
             _ -> die $ "Record constructor " ++ Msg.quote qname ++ " is not declared in environment!"

    convert' pragmas (Hsx.RecUpdate _ exp updates) = 
        do exp' <- convert pragmas exp
           fstupd:upds <- mapM convUpd updates
           let updateFunction = Isa.Parenthesized (foldr comp fstupd upds)
           return $ Isa.App updateFunction exp'
       where comp a b = Isa.App (Isa.App (Isa.Const (Isa.Name "\\<circ>" {- FIXME use a lookup in the adaption table instead of the raw string -})) a) b
             convUpd (Hsx.FieldUpdate _ fname fexp) =
                                do fexp' <- convert pragmas fexp
                                   let ufun = Isa.Const (Isa.Name ("update_" ++ unqual fname))
                                   return $ Isa.App ufun fexp'
             unqual (Hsx.Qual _ _ n) = uname n
             unqual (Hsx.UnQual _ n) = uname n
             uname (Hsx.Ident _ n) = n
             uname (Hsx.Symbol _ n) = n

    convert' pragmas (Hsx.If _ t1 t2 t3)
        = do t1' <- convert pragmas t1; t2' <- convert pragmas t2; t3' <- convert pragmas t3
             return (Isa.If t1' t2' t3')

    convert' pragmas (Hsx.Case _ exp alts)
        = do exp'  <- convert pragmas exp
             alts' <- mapM (convert pragmas) alts
             return $ Isa.Case exp' alts'

    convert' pragmas x@(Hsx.Lambda _loc pats body)
        = do patsNames  <- mapM (convert pragmas) pats
             let (pats', aliases) = unzip patsNames
                 aliases' = concat aliases
             body'  <- convert pragmas body
             let body'' = mkSimpleLet aliases' body'
             if all isConst pats' then return $ makeAbs [n | Isa.Const n <- pats'] body''
                                else makePatternMatchingAbs pats' body''
          where isConst (Isa.Const _)   = True
                isConst _             = False

    convert' pragmas expr@(Hsx.Let _ (Hsx.BDecls _ bindings) body)
        = let (_, patbindings) = partition isTypeSig bindings
          in assert (all isPatBinding patbindings)
             $ do let (pats, rhss) = unzip (map (\(Hsx.PatBind _ pat rhs _) -> (pat, rhs)) patbindings)
                  patsNames <- mapM (convert pragmas) pats
                  let (pats', aliases) = unzip patsNames
                  rhss' <- mapM (convert pragmas) rhss
                  let rhss'' = zipWith mkSimpleLet aliases rhss'
                  body' <- convert pragmas body
                  return (Isa.Let (zip pats' rhss'') body')
          where isTypeSig (Hsx.TypeSig _ _ _)      = True
                isTypeSig _                      = False
                isPatBinding (Hsx.PatBind _ _ _ (Just (Hsx.BDecls _ []))) = True
                isPatBinding (Hsx.PatBind _ _ _ Nothing)                = True
                isPatBinding _                   = False
                
    convert' pragmas (Hsx.ListComp _ e stmts) 
        = do e'     <- convert pragmas e
             stmts' <- liftM concat $ mapM convertListCompStmt stmts
             return (Isa.ListCompr e' stmts')
        where convertListCompStmt (Hsx.QualStmt _ (Hsx.Qualifier _ b))     = convert pragmas  b >>= (return . (:[]) . Isa.Guard)
              convertListCompStmt (Hsx.QualStmt _ (Hsx.Generator _ p e)) = do
                (p',as) <- convert pragmas p
                let gens = mkSimpleGens as
                e' <- convert pragmas e
                return $ [Isa.Generator (p', e')] ++ gens
              convertListCompStmt _
                  = die "Such statements not supported in List Comprehensions."
              mkSimpleGens = map (\(n,t) -> Isa.Generator (Isa.Const n, mkList [t]))
    convert' pragmas (Hsx.Do _ stmts)
        = do isaStmts <- liftM concat $ mapM (convert pragmas) stmts
             mbDo <- getCurrentMonadDoSyntax
             case mbDo of
               Nothing -> die "Do syntax is used without sufficient type information!"
               Just (DoParen pre post) -> 
                   return $ Isa.DoBlock pre isaStmts post

    convert' pragmas junk = pattern_match_exhausted "Hsx.Exp () -> Isa.Term" junk

instance Convert (Hsx.Stmt ()) [Isa.DoBlockFragment] where

    convert' pragmas (Hsx.Generator _ pat exp) = 
        do exp' <- convert pragmas exp
           (pat', aliases) <- convert pragmas pat
           aliases' <- mkDoLet pragmas aliases
           return (Isa.DoGenerator pat' exp' : aliases')
    convert' pragmas (Hsx.Qualifier _ exp) = liftM ( (:[]) . Isa.DoQualifier) (convert pragmas exp)
    convert' pragmas (Hsx.LetStmt _ binds) =
        case binds of
          Hsx.BDecls _ [Hsx.PatBind _ pat (Hsx.UnGuardedRhs _ exp) _] ->
              do exp' <- convert pragmas exp
                 (pat', aliases) <- convert pragmas pat
                 aliases' <- mkDoLet pragmas aliases
                 ret <- mkReturn pragmas
                 return (Isa.DoGenerator pat' (Isa.App ret exp') : aliases')
             -- liftM2 Isa.DoGenerator (convert pat) (convert (Hsx.App (Hsx.Var (Hsx.UnQual (Hsx.Ident "return"))) exp))
          def -> pattern_match_exhausted "Hsx.Stmt -> Isa.DoBlockFragment" def

mkReturn :: [Pragma] -> ContextM Isa.Term
mkReturn pragmas = convert pragmas . Hsx.Var () . Hsx.UnQual () .Hsx.Ident () $ "return"

mkDoLet :: [Pragma] -> [(Isa.Name, Isa.Term)] -> ContextM [Isa.DoBlockFragment]
mkDoLet pragmas aliases = 
    do ret <- mkReturn pragmas
       let mkSingle (name, term) = Isa.DoGenerator (Isa.Const name) (Isa.App ret term)
       return $ map mkSingle aliases

{-|
  We desugare lambda expressions to true unary functions, i.e. to
  lambda expressions binding only one argument.
 -}
makeAbs :: [Isa.Name] -> Isa.Term -> Isa.Term
makeAbs varNs body
    = assert (not (null varNs)) $ foldr Isa.Abs body varNs

{-|
  Since HOL doesn't have true n-tuple constructors (it uses nested
  pairs to represent n-tuples), we simply return a lambda expression
  that takes n parameters and constructs the nested pairs within its
  body.
 -}

makeTupleDataCon :: [Pragma] -> Int -> ContextM Isa.Term
makeTupleDataCon pragmas n     -- n < 2  cannot happen (cf. Language.Haskell.Exts.Hsx.TupleCon)
    = assert (n > 2) $ -- n == 2, i.e. pairs, can and are dealt with by usual conversion.
      do argNs  <- mapM (liftGensym . Gensym.genHsQName) (replicate n (Hsx.UnQual () (Hsx.Ident () "arg")))
         args   <- return (map (Hsx.Var ()) argNs)
         argNs' <- mapM (convert pragmas) argNs
         args'  <- convert pragmas (Hsx.Tuple () Hsx.Boxed args)
         return $ Isa.Parenthesized (makeAbs argNs' args')
    where pair x y = Hsx.App () (Hsx.App () (Hsx.Con () (Hsx.Special () (Hsx.TupleCon () Hsx.Boxed 2))) x) y

{-|
  HOL does not support pattern matching directly within a lambda
  expression, so we transform a @Hsx.Abs pat1 pat2 .. patn -> body@ to
  
  @
  Isa.Abs g1 .
     Isa.Case g1 of pat1' =>
       Isa.Abs g2 .
         Isa.Case g2 of pat2' => ... => Isa.Abs gn .
                                          Isa.Case gn of patn' => body'
  @
  where @g1@, ..., @gn@ are fresh identifiers.
-}
makePatternMatchingAbs :: [Isa.Pat] -> Isa.Term -> ContextM Isa.Term
makePatternMatchingAbs patterns theBody
    = foldM mkMatchingAbs theBody (reverse patterns) -- foldM is a left fold.
      where mkMatchingAbs body pat
                = do g <- liftGensym (Gensym.genIsaName (Isa.Name "arg"))
                     return $ Isa.Abs g (Isa.Case (Isa.Const g) [(pat, body)])


makeRecordCmd :: [Pragma] -> Hsx.Name ()  -- ^type constructor
              -> [Hsx.Name ()] -- ^type variable arguments to the constructor
              -> [Hsx.ConDecl ()] -- ^a singleton list containing a record declaration
              -> ContextM Isa.Stmt   -- ^the resulting record declaration
makeRecordCmd pragmas tyconN tyvarNs [Hsx.RecDecl _ name slots] -- cf. `isRecDecls'
    = do tycon  <- convert pragmas tyconN
         tyvars <- mapM (convert pragmas) tyvarNs
         slots' <- mapsM cnvSlot slots
         return $ Isa.Record (Isa.TypeSpec tyvars tycon) slots'
    where cnvSlot (Hsx.FieldDecl _ names typ)
              = do names' <- mapM (convert pragmas) names
                   typ'   <- convert pragmas typ
                   return (zip names' (cycle [typ']))
 

{-|
  Hsx parses every infix application simply from left to right without
  taking operator associativity or binding priority into account. So
  we gotta fix that up ourselves. (We also properly consider infix
  declarations to get user defined operator right.)
-}
fixOperatorFixities :: Hsx.Exp () -> ContextM (Hsx.Exp ())

-- Notice that `1 * 2 + 3 / 4' is parsed as `((1 * 2) + 3) / 4', i.e.
-- 
--    Hsx.InfixApp (Hsx.InfixApp (Hsx.InfixApp 1 * 2) + 3) / 4
--
-- whereas `1 * 2 + (3 / 4)' is parsed as
--
--    Hsx.InfixApp (Hsx.InfixApp 1 * 2) + (HsParen (Hsx.InfixApp 3 / 4))
--
-- and `1 * (2 + 3) / 4' is parsed as
--
--    Hsx.InfixApp (Hsx.InfixApp 1 (HsParen (Hsx.InfixApp 2 + 3))) / 4
--
-- Thus we _know_ that the second operand of an infix application,
-- i.e. the e2 in `Hsx.InfixApp e1 op e2', can _never_ be a bare infix
-- application that we might have to consider during fixup.
--  
fixOperatorFixities app@(Hsx.InfixApp _ (Hsx.InfixApp _ e1 op1 e2) op2 e3)
    -- We assume that `(e1, op1, e2)' is correct already
    -- and from above, we also know that `e3' cannot possibly
    -- interfere, so we just have to find the proper place of `op2'.
    = do (assoc1', prio1)  <- lookupInfixOp op1
         (assoc2', prio2)  <- lookupInfixOp op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (Hsx.InfixApp () e1 op1) (fixOperatorFixities (Hsx.InfixApp () e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Hsx.AssocLeft _  -> return app
                        Hsx.AssocRight _ -> return (Hsx.InfixApp () e1 op1 (Hsx.InfixApp () e2 op2 e3))
                        Hsx.AssocNone _  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities nonNestedInfixApp = return nonNestedInfixApp


{-|
  Hsx parses every infix application simply from left to right without
  taking operator associativity or binding priority into account. So
  we gotta fix that up ourselves. (We also properly consider infix
  declarations to get user defined operator right.)
-}
fixOperatorFixities' :: Hsx.Pat () -> ContextM (Hsx.Pat ())
fixOperatorFixities' app@(Hsx.PInfixApp _ (Hsx.PInfixApp _ e1 op1 e2) op2 e3)
    = do (assoc1', prio1)  <- lookupInfixOpName op1
         (assoc2', prio2)  <- lookupInfixOpName op2
         let assoc1 = normalizeAssociativity assoc1'
         let assoc2 = normalizeAssociativity assoc2'
         case prio1 `compare` prio2 of
           GT -> return app
           LT -> liftM (Hsx.PInfixApp () e1 op1) (fixOperatorFixities' (Hsx.PInfixApp () e2 op2 e3))
           EQ -> if assoc2 /= assoc1 then
                     die (Msg.assoc_mismatch op1 assoc1 op2 assoc2)
                 else case assoc2 of
                        Hsx.AssocLeft _  -> return app
                        Hsx.AssocRight _ -> return (Hsx.PInfixApp () e1 op1 (Hsx.PInfixApp () e2 op2 e3))
                        Hsx.AssocNone _  -> die ("fixupOperatorFixities: Internal error " ++
                                               "(AssocNone should have already been normalized away.)")
fixOperatorFixities' nonNestedInfixApp = return nonNestedInfixApp


{-|
  Enforces left associativity as default.
-}
normalizeAssociativity :: Hsx.Assoc () -> Hsx.Assoc ()
normalizeAssociativity (Hsx.AssocNone _) = Hsx.AssocLeft () -- as specified in Haskell98.
normalizeAssociativity etc = etc

{-|
  This function looks up the lexical information for the
  given constant identifier.
-}
lookupIdentifier_Constant :: Hsx.QName () -> ContextM (Maybe Ident_Env.Identifier)
lookupIdentifier_Constant qname
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Ident_Env.lookupConstant (Ident_Env.fromHsk modul) (Ident_Env.fromHsk qname) globalEnv)

{-|
  This function looks up the lexical information for the given
  type identifier.
-}
lookupIdentifier_Type' :: Ident_Env.Name -> ContextM (Maybe Ident_Env.Identifier)
lookupIdentifier_Type' envName
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Ident_Env.lookupType (Ident_Env.fromHsk modul) envName globalEnv)
{-|
  This function looks up the lexical information for the given
  type identifier.
-}
lookupIdentifier_Type :: Hsx.QName () -> ContextM (Maybe Ident_Env.Identifier)
lookupIdentifier_Type qname
    = do globalEnv <- queryContext globalEnv
         modul     <- queryContext currentModule
         return (Ident_Env.lookupType (Ident_Env.fromHsk modul) (Ident_Env.fromHsk qname) globalEnv)

{-|
  This function looks up the fixity declaration for the given
  infix operator.
-}
lookupInfixOp :: Hsx.QOp () -> ContextM (Hsx.Assoc (), Maybe Int)
lookupInfixOp = lookupInfixOpName . qop2name
    where qop2name (Hsx.QVarOp _ n) = n
          qop2name (Hsx.QConOp _ n) = n
{-|
  This function looks up the fixity declaration for the given
  infix operator.
-}
lookupInfixOpName :: Hsx.QName () -> ContextM (Hsx.Assoc (), Maybe Int)
lookupInfixOpName qname
    = do identifier <- lookupIdentifier_Constant (qname)
         case identifier of
           Just (Ident_Env.Constant (Ident_Env.InfixOp _ envassoc prio)) 
                   -> return (Ident_Env.toHsk envassoc, prio)
           Nothing -> do globalEnv <- queryContext globalEnv;
                         warn (Msg.missing_infix_decl qname globalEnv)
                         return (Hsx.AssocLeft (), Just 9) -- default values in Haskell98
    where qop2name (Hsx.QVarOp _ n) = n
          qop2name (Hsx.QConOp _ n) = n


{-|
  This function looks up the type for the given identifier.
-}
lookupType :: Hsx.QName () -> ContextM (Maybe (Hsx.Type ()))
lookupType fname = do
  identifier <- lookupIdentifier_Constant fname
  case identifier of
    Nothing -> return Nothing
    Just id -> let typscheme = Ident_Env.typschemeOf (Ident_Env.lexInfoOf id) 
               in if snd typscheme == Ident_Env.TyNone
                  then return Nothing else return $ Just (Ident_Env.hsk_typ_of_typscheme typscheme)


-- A Conversion Unit

{-|
  This data structure combines several Haskell modules and the corresponding environment.
  into one coherent unit.
-}
type HskModulePragma = (Hsx.Module Hsx.SrcLoc, [Hsx.UnknownPragma])
data HskUnit = HskUnit [HskModulePragma] CustomTranslations Ident_Env.GlobalE
  deriving (Show)

{-|
  This data structure combines several Isabelle theories and the corresponding environment
  into one coherent unit.
-}
data IsaUnit = IsaUnit [Isa.Module] [CustomTheory] Ident_Env.GlobalE
  deriving (Show)

newtype Conversion a = Conversion (ReaderT Config IO a)
    deriving (Functor, Applicative, Monad, MonadReader Config, MonadIO, MonadError IOError)

isCustomModule :: Hsx.ModuleName () -> Conversion Bool
isCustomModule
    = liftM isJust . getCustomTheory

getCustomisations :: Conversion Customisations
getCustomisations = ask >>= return . customisations

getCustomTheory :: Hsx.ModuleName () -> Conversion (Maybe CustomTheory)
getCustomTheory mod =
    ask >>= return . (`Config.getCustomTheory` mod) . customisations

getInputFilesRecursively :: Conversion [FilePath]
getInputFilesRecursively
    = do config <- ask
         let locs = inputLocations config
         liftIO $ liftM concat $ mapM getFiles locs
    where getFiles :: Location -> IO [FilePath]
          getFiles (FileLocation path)
              = do fileEx <- doesFileExist path
                   if fileEx
                     then return [path]
                     else do dirEx <- doesDirectoryExist path
                             if dirEx
                               then getFilesRecursively path
                               else hPutStrLn stderr ("Warning: File or directory \"" ++ path ++ "\" does not exist!") >> return []  

     
{-|
  This function recursively searches the given directory for Haskell source files.
-}
getFilesRecursively :: FilePath -> IO [FilePath]
getFilesRecursively dir = traverseDir dir action
    where action fp = return fp

{-|
  This function traverses the file system beneath the given path executing the given
  action at every file and directory that is encountered. The result of each action is
  accumulated to a list which is returned.
-}
traverseDir :: FilePath -> (FilePath -> IO a) -> IO [a]
traverseDir dirpath op = do
  fps <- getDirectoryContents dirpath `catchIO` const (return [])
  let fps' = map (combine dirpath) . filter (`notElem` [".", ".."]) $ fps
  fmap concat $ mapM work fps'
      where work f = do
              res <- op f
              res' <- traverseDir f op
              return $ res:res'

getOutputDir :: Conversion (Maybe FilePath)
getOutputDir = ask >>= return . fmap fileLocation . outputLocation

getExportCode :: Conversion Bool
getExportCode = ask >>= return . exportCode

getTryImport :: Conversion Bool
getTryImport = ask >>= return . tryImport

getOnlyTypes :: Conversion Bool
getOnlyTypes = ask >>= return . onlyTypes

getBasePathAbs :: Conversion (Maybe FilePath)
getBasePathAbs = ask >>= return . basePathAbs

getIgnoreNotInScope :: Conversion Bool
getIgnoreNotInScope = ask >>= return . ignoreNotInScope

getAbsMutParams :: Conversion Bool
getAbsMutParams = ask >>= return . absMutParams

runConversion :: Config -> Conversion a -> IO a
runConversion config (Conversion parser) = runReaderT parser config


{-|
  This function takes a parsed Haskell module and produces a Haskell unit by parsing
  all module imported by the given module and add including the initial global environment
  as given by 'Ident_Env.initialGlobalEnv'.
-}
parseHskFiles :: Bool -> Bool -> Maybe FilePath -> [HaskellDocument] -> Conversion [HskUnit]
parseHskFiles tryImport onlyTypes basePathAbs paths
    = do (hsmodules,custTrans) <- parseFilesAndDependencies tryImport basePathAbs paths
         (depGraph, fromVertex, _) <- makeDependencyGraph hsmodules
         let cycles = cyclesFromGraph depGraph
         when (not (null cycles)) -- not a DAG?
              $ let toModuleName v = case fromVertex v of (_, Hsx.ModuleName _ n,_) -> n
                in fail (Msg.cycle_in_dependency_graph (map toModuleName (head cycles)))
         let toModule v = case fromVertex v of (m,_,_) -> m
         case map (map toModule . flatten) (components depGraph) of
           -- this should not happen
           [] -> fail $ "Internal error: No Haskell module was parsed!"
           modss -> 
               let mkUnit mods = HskUnit mods custTrans Ident_Env.initialGlobalEnv
               in return $ map (mkUnit . if onlyTypes then G.everywhere (G.mkT filter_decl) else id) modss
  where filter_decl :: [Hsx.Decl Hsx.SrcLoc] -> [Hsx.Decl Hsx.SrcLoc]
        filter_decl = concatMap (\t -> case t of Hsx.TypeDecl _ _ _ -> [t]
                                                 Hsx.DataDecl _ _ _ _ _ _ -> [t]
                                                 _ -> [])

{-|
  This function computes a list of all cycles in the given graph.
  The cycles are represented by the vertexes which constitute them.
-}
cyclesFromGraph :: Graph -> [[Vertex]]
cyclesFromGraph graph
    = filter ((>1) . length) $ map flatten (scc graph)

{-|
  This function computes the graph depicting the dependencies between all modules
  imported by the given module plus itself. The result comes with two functions to convert
  between the modules an the vertices of the graph (as provided by 'Data.Graph.graphFromEdges').
-}
makeDependencyGraph ::  [HskModulePragma]
                    -> Conversion (Graph,
                          Vertex -> (HskModulePragma, Hsx.ModuleName (), [Hsx.ModuleName ()]),
                          Hsx.ModuleName () -> Maybe Vertex)
makeDependencyGraph hsmodules
    = do edges <- mapM makeEdge $ Hsx.zipMod0 fst hsmodules
         return $ graphFromEdges edges
    where makeEdge (modul, hsmodule@(Hsx.Module _ _ _ imports _, _))
              = do let imported_modules = map (Hsx.importModule . Hsx.fmapUnit) imports
                   imported_modules'  <- filterM isCustomModule imported_modules
                   return (hsmodule, modul, imported_modules)

type HaskellDocument = Either FilePath String
type ModuleImport = (HaskellDocument, Maybe (Hsx.ModuleName ()))

data GrovelS = GrovelS{gVisitedPaths :: Set FilePath,
                       gRemainingPaths :: [ModuleImport],
                       gParsedModules :: [HskModulePragma],
                       gCustTrans :: CustomTranslations,
                       gTryImport :: Bool,
                       gBasePathAbs :: Maybe FilePath}

newtype GrovelM a = GrovelM (StateT GrovelS Conversion a)
    deriving (Monad, Functor, Applicative, MonadState GrovelS, MonadIO)



liftConv :: Conversion a -> GrovelM a 
liftConv = GrovelM . lift

checkVisited :: FilePath -> GrovelM Bool
checkVisited path = liftM (Set.member path . gVisitedPaths) get

getTryImport' :: GrovelM Bool
getTryImport' = liftM gTryImport get

getBasePathAbs' :: GrovelM (Maybe FilePath)
getBasePathAbs' = liftM gBasePathAbs get

addModule :: Hsx.SrcLoc -> HskModulePragma -> GrovelM ()
addModule loc mod
    = modify (\ state@(GrovelS{gVisitedPaths = visited, gParsedModules = mods}) -> 
              state{gVisitedPaths = Set.insert (Hsx.srcFilename loc)  visited, gParsedModules = mod:mods})

addImports :: [ModuleImport] -> GrovelM ()
addImports imps = modify (\state@(GrovelS{gRemainingPaths = files}) -> state{gRemainingPaths = imps ++ files})
                  
{-|
  This function checks if the given module is a custom module. If it
  is it is added to the set of custom modules in the state and @True@
  is returned. Otherwise just @False@ is returned.
-}       
-- addCustMod :: Hsx.ModuleName () -> GrovelM Bool
addCustMod mod =
    do state <- get
       mbCustThy <- liftConv $ getCustomTheory mod
       case mbCustThy of
         Nothing -> return False
         Just custThy ->
             put state{gCustTrans = Map.insert mod custThy (gCustTrans state)}
                 >> return True
         
{-|
  Same as 'addCustMod' but @True@ and @False@ are swapped.
-}
addCustMod' :: Hsx.ModuleName () -> GrovelM Bool 
addCustMod' = liftM not . addCustMod
                   
nextImport :: GrovelM (Maybe ModuleImport)
nextImport =
    do state <- get
       case gRemainingPaths state of
         [] -> return Nothing
         p:ps ->
             do put $ state{gRemainingPaths = ps}
                return$ Just p

parseFilesAndDependencies :: Bool -> Maybe FilePath -> [HaskellDocument] -> Conversion ([HskModulePragma],CustomTranslations)
parseFilesAndDependencies tryImport basePathAbs files = 
    let GrovelM grovel = grovelImports
        mkImp file = (file,Nothing)
        imps = map mkImp files
        state = GrovelS Set.empty imps [] Map.empty tryImport basePathAbs
    in do state' <- execStateT grovel state
          return (gParsedModules state' , gCustTrans state')

grovelImports :: GrovelM ()
grovelImports = 
    do mbFile <- nextImport
       case mbFile of
         Nothing -> return ()
         Just file -> grovelFile file

grovelFile :: ModuleImport -> GrovelM ()
grovelFile imp@(Left file,_) = 
    do v <- checkVisited file
       if v 
        then grovelImports
        else parseHskFile imp

grovelFile imp@(Right _,_) = parseHskFile imp

-- grovelModule :: Hsx.ModuleName () -> GrovelM ()
grovelModule loc hsmodule@(Hsx.Module _ baseMod _ imports _, _) = 
    do let newModules = map Hsx.importModule imports
       realModules <- filterM addCustMod' newModules
       basePathAbs <- getBasePathAbs'
       let modImps = map (mkModImp basePathAbs) realModules
       tryImport <- getTryImport'
       modImps' <- liftIO $ mapM (checkImp tryImport) modImps
       addImports $ concatMap id modImps'
       grovelImports
    where baseLoc = Hsx.srcFilename loc
          mkModImp basePathAbs mod = (computeSrcPath baseMod (baseLoc, basePathAbs) mod, Just mod)
          checkImp tryImport (file,Just mod) =
              do ext <- doesFileExist file
                 if ext then return $ [(Left file, Just mod)]
                        else do
                               (if tryImport then hPutStrLn stderr else fail)
                                  $ "The module \"" ++ Hsx.showModuleName mod
                                 ++ maybe "" (\(Hsx.ModuleHead _ baseMod _ _) -> "\" imported from module \"" ++ Hsx.showModuleName baseMod) baseMod
                                 ++ "\" cannot be found at \"" ++ file ++ "\"!"
                               return []

{-|
  This function computes the path where to look for an imported module.
-}

computeSrcPath :: Maybe (Hsx.ModuleHead ())      -- ^the module that is importing
               -> (FilePath, Maybe FilePath)     -- ^the path to the importing module
               -> Hsx.ModuleName ()       -- ^the module that is to be imported
               -> FilePath     -- ^the assumed path to the module to be imported
computeSrcPath importingMod (basePath, basePathAbs) m
    = let baseDir = shrinkPath . joinPath $ maybe (splitPath (takeDirectory basePath) ++ replicate (maybe 0 (\(Hsx.ModuleHead _ m _ _) -> Hsx.moduleHierarchyDepth m) importingMod) "..") splitPath basePathAbs
      in combine baseDir (Hsx.module2FilePath m)   

shrinkPath :: FilePath -> FilePath
shrinkPath = joinPath . shrinkPath' . splitPath
    where shrinkPath' [] = []
          shrinkPath' [x] = [x]
          shrinkPath' (x:y:xs)
              | x /= "/" && y `elem` ["..", "../"] = shrinkPath' xs
              | otherwise = x : shrinkPath' (y:xs)
    
parseHskFile :: ModuleImport -> GrovelM ()
parseHskFile (file, mbMod)  = 
    do result <- let extensions = [Hsx.EnableExtension Hsx.ExplicitForAll] in
                 case file of
                   Left file -> liftIO $ Hsx.parseFileWithCommentsAndPragmas (Hsx.defaultParseMode { Hsx.extensions = extensions, Hsx.parseFilename = file }) file
                                `catchIO` (\ioError -> fail $ "An error occurred while reading module file \"" ++ file ++ "\": " ++ show ioError)
                   Right cts -> return $ parseFileContentsWithCommentsAndPragmas (Hsx.defaultParseMode { Hsx.extensions = extensions }) cts
       (loc, mod@(Hsx.Module _ name _ _ _, _)) <-
         case result of
           (Hsx.ParseFailed loc msg) ->
               fail $ "An error occurred while parsing module file: " ++ Msg.failed_parsing loc msg
           (Hsx.ParseOk (m@(Hsx.Module loc mName _ _ _), _, pragma)) ->
               let m' = fmap Hsx.getPointLoc m in
               case (file, mbMod) of
                 (Left file, Just expMod) ->
                     case mName of
                       (Just (Hsx.ModuleHead _ mName _ _)) ->
                         if Hsx.fmapUnit mName == expMod
                         then return (Hsx.getPointLoc loc, (m', pragma))
                         else fail $ "Name mismatch: Name of imported module in \"" 
                                  ++ file ++"\" is " ++ Hsx.showModuleName (Hsx.fmapUnit mName)
                                          ++ ", expected was " ++ Hsx.showModuleName expMod
                 _ -> return (Hsx.getPointLoc loc, (m', pragma))
       cust <- case name of Nothing -> return False
                            Just (Hsx.ModuleHead _ name _ _) -> addCustMod $ Hsx.fmapUnit name
       if cust then grovelImports
               else addModule loc mod
                    >> grovelModule loc (case mod of (m, u) -> (Hsx.fmapUnit m, u))

-- | Converts a parse result with comments to a parse result with comments and
--   unknown pragmas.
--   (Adapted from haskell-src-exts)
separatePragmas :: Hsx.ParseResult (Hsx.Module Hsx.SrcSpanInfo, [Hsx.Comment])
                -> Hsx.ParseResult (Hsx.Module Hsx.SrcSpanInfo, [Hsx.Comment], [Hsx.UnknownPragma])
separatePragmas r =
    case r of
        Hsx.ParseOk (m, comments) ->
            let (pragmas, comments') = partition pragLike comments
              in  Hsx.ParseOk (m, comments', map commentToPragma pragmas)
                where commentToPragma (Hsx.Comment _ l s) =
                            Hsx.UnknownPragma l $ init $ drop 1 s
                      pragLike (Hsx.Comment b _ s) = b && pcond s
                      pcond s = length s > 1 && take 1 s == "#" && last s == '#'
        Hsx.ParseFailed l s ->  Hsx.ParseFailed l s

-- | Parse a source file from a string using a custom parse mode retaining comments
--   as well as unknown pragmas.
--   (Adapted from haskell-src-exts)
parseFileContentsWithCommentsAndPragmas
  :: Hsx.ParseMode -> String
  -> Hsx.ParseResult (Hsx.Module Hsx.SrcSpanInfo, [Hsx.Comment], [Hsx.UnknownPragma])
parseFileContentsWithCommentsAndPragmas pmode str = separatePragmas parseResult
    where parseResult = Hsx.parseFileContentsWithComments pmode str
