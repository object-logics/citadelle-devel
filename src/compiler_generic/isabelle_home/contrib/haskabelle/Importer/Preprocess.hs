{-# LANGUAGE 
  GeneralizedNewtypeDeriving,
  ScopedTypeVariables #-}

{-| Author:     Tobias C. Rittweiler, TU Muenchen

-}

module Importer.Preprocess (isEmptyBinds, preprocessModule) where

import Importer.Library
import Data.Function
import Data.Maybe
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
import Data.Graph
import Data.Tree

import Data.Generics
import Data.Generics.Biplate
import Data.Generics.Str

import Control.Monad.Reader (ReaderT, MonadReader, ask, runReaderT, runReader, Reader)
import Control.Monad.Writer (WriterT, MonadWriter, tell, runWriterT, lift, MonadFix)

import Importer.Env

import qualified Importer.Gensym as Gensym
import qualified Importer.Msg as Msg

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Hsx as Hsx


-- import Importer.Test.Generators
-- import Test.QuickCheck
-- import qualified Test.QuickCheck.Monadic as QC (assert)
-- import Test.QuickCheck.Monadic hiding (assert)

type HskDecl = (Int, Hsx.Decl ())

{-|
  This function preprocesses the given Haskell module to make things easier for the
  conversion.
-}
preprocessModule :: [String] -> Hsx.Module () -> Hsx.Module ()
preprocessModule reserved (Hsx.Module l modul pragmas imports topdecls) =
  Hsx.Module l modul pragmas imports topdecls4 where
    topdecls1 =  map (whereToLet .  deguardify) topdecls
    ((topdecls2, topdecls2'), gensymcount) 
                 = Gensym.runGensym Gensym.countInit (evalDelocaliser Set.empty (delocaliseAll (zip [Gensym.posInit ..] topdecls1)))
    topdecls3 = topdecls2'
              & foldl (\m (pos, decl) -> Map.insertWith (++) pos [decl] m)
                      (Map.fromList (map (\(pos, x) -> (pos, [x])) topdecls2))
              & Map.toList
              & concatMap snd
    topdecls4 = Gensym.evalGensym gensymcount (mapM (normalizeNames_Decl reserved) topdecls3)


{-|
  /Delocalization of Hsx.Decls/

  Since Isabelle/HOL does not really support local function
  declarations, we convert the Haskell AST to an equivalent AST
  where every local function declaration is made a global
  declaration. This includes where as well as let expressions.

  Additionally, all variables defined in a where clause
  are converted to an equivalent let expression.


  We keep track of the names that are directly bound by a declaration,
  as functions must not close over them. See below for an explanation.
 -}
newtype DelocaliserM a = DelocaliserM (ReaderT Hsx.HskNames (WriterT [HskDecl] Gensym.GensymM) a)
    deriving (Monad, Functor, Applicative, MonadFix, MonadReader Hsx.HskNames, MonadWriter [HskDecl])

{-instance MonadWriter [HskDecl] DelocaliserM where
    tell _ = error ""
    listen _ = error ""
    pass _ = error ""

[HskDecl] -> DelocaliserM ()
DelocaliserM a -> DelocaliserM (a, [HskDecl])
DelocaliserM (a, [HskDecl] -> [HskDecl]) -> DelocaliserM a-}

addTopDecls :: [Hsx.Decl ()] -> DelocaliserM ()
addTopDecls decls = do pos <- liftGensym Gensym.askPos
                       tell $ zip (repeat pos) decls

addTopDecl :: Hsx.Decl () -> DelocaliserM ()
addTopDecl = addTopDecls . (:[])

liftGensym :: Gensym.GensymM a -> DelocaliserM a
liftGensym = DelocaliserM . lift . lift


{-|
  This function executes the given delocaliser monad starting with an
  empty list of bound variables.
-}
evalDelocaliser :: Hsx.HskNames -> DelocaliserM a -> Gensym.GensymM (a,[HskDecl]) 
evalDelocaliser state (DelocaliserM sm) =
    let wm = runReaderT sm state in
    runWriterT wm

delocaliseAll :: GenericM DelocaliserM
delocaliseAll = everywhereEnv Hsx.boundNamesEnv delocalise

delocalise :: GenericM DelocaliserM
delocalise = mkM delocaliseLet
             `extM` delocaliseClsDecl
             `extM` delocaliseDecl

delocaliseDecl :: HskDecl -> DelocaliserM HskDecl
delocaliseDecl (pos, decl) =
    do liftGensym $ Gensym.setPos pos
       return (pos, decl)

delocaliseClsDecl :: Hsx.ClassDecl () -> DelocaliserM (Hsx.ClassDecl ())
delocaliseClsDecl clsDecl@(Hsx.ClsDecl _ decl) = 
    do addTopDecl decl
       return clsDecl

{-|
  This data structure is supposed to comprise the definition
  of a function and possibly its type signature declaration.
-}
data FunDef = FunDef { funBind :: Hsx.Decl (), funSig :: Maybe (Hsx.Decl ()), funFreeNames :: Hsx.HskNames}

funName :: FunDef -> Hsx.QName ()
funName FunDef{funBind = Hsx.FunBind _ (Hsx.Match _ name _ _ _  : _)} = Hsx.UnQual () name

{-|
  This function renames the function name of the given function definition.
-}
renameFunDef :: [Hsx.Renaming] -> FunDef -> FunDef
renameFunDef ren def@(FunDef{ funBind = bind, funSig = sig})
    = let bind' = Hsx.renameDecl ren bind
          sig' = liftM (Hsx.renameDecl ren) sig
      in def{ funBind = bind', funSig = sig'}

{-|
  This function partitions bindings into a pair (signature declarations, other bindings)
-}
groupFunDefs :: [Hsx.Decl ()] -> [FunDef]
groupFunDefs decls = 
    let (funBinds,funSigs) = partition isFunBind decls
        funSigs' = concatMap flattenTypeSig funSigs
        sigMap = Map.fromList $ map sigName funSigs'
        mkFunDef bind@(Hsx.FunBind _ (Hsx.Match _ name _ _ _ : _))
            = FunDef bind (Map.lookup name sigMap) (Hsx.extractFreeVarNs bind)
    in map mkFunDef funBinds
    where isFunBind (Hsx.FunBind _ _) = True
          isFunBind _ = False
          sigName decl@(Hsx.TypeSig _ [name] _) = (name,decl)


funDefComponents :: [FunDef] -> [[FunDef]]
funDefComponents funDefs =
   let names = Set.fromList $ map funName funDefs
       graphConstr = map graphComp funDefs
       graphComp funDef = (funDef, funName funDef, Set.toList . Set.intersection names . funFreeNames $ funDef)
       (graph, extr,_) = graphFromEdges graphConstr
       forest = components graph
    in map (map ((\(n,_,_) -> n) . extr) . flatten) forest

{-|
  This function adds an additional argument to the given match that contains the
  environment of a closure.
-}
addEnvArgToMatch :: Hsx.Name ()  -- ^the name of the environment variable
          -> [Hsx.Name ()] -- ^the names of the variables in the environment
          -> Hsx.Match ()  -- ^the match that should be enriched by an environment argument
          -> Hsx.Match ()  -- ^the resulting match
addEnvArgToMatch envName closureNames match@(Hsx.Match loc name pats rhs binds)
    = let boundNames = map uname (Hsx.extractBindingNs pats)
          toPat name = if name `elem` boundNames
                       then Hsx.PWildCard ()
                       else Hsx.PVar () name
          allBound = all (`elem` boundNames) closureNames
          tuple = case closureNames of
                    [closureName] -> toPat closureName
                    _ -> Hsx.PTuple () Hsx.Boxed (map toPat closureNames)
          passing = (Hsx.UnQual () envName) `Set.member` Hsx.extractFreeVarNs match
          envArg = if passing then if allBound
                                   then Hsx.PVar () envName
                                   else Hsx.PAsPat () envName tuple
                   else if allBound
                        then Hsx.PWildCard ()
                        else tuple
      in (Hsx.Match loc name (envArg : pats) rhs binds)
    where uname (Hsx.Qual _ _ name) = name
          uname (Hsx.UnQual _ name) = name

{-|
  This function adds an additional argument to the given function binding that contains the
  environment of a closure.
-}
addEnvArgToDecl :: Hsx.Name ()  -- ^the name of the environment variable
                -> [Hsx.Name ()] -- ^the names of the variables in the environment
                -> Hsx.Decl ()  -- ^the match that should be enriched by an environment argument
                -> Hsx.Decl ()  -- ^the resulting match
addEnvArgToDecl envName closureNames (Hsx.FunBind l matches)
    = let matches' = map (addEnvArgToMatch envName closureNames) matches
      in Hsx.FunBind l matches'

addPatBindsToMatch :: [Hsx.Decl ()] -> Hsx.Match () -> Hsx.Match ()
addPatBindsToMatch patBinds match@(Hsx.Match loc name pats (Hsx.UnGuardedRhs _ exp) binds)
    = let neededPatBinds = filter patBindNeeded patBinds
          shadowedPatBinds = map shadowPatBind neededPatBinds
          rhs' = Hsx.UnGuardedRhs () (Hsx.Let () (Hsx.BDecls () shadowedPatBinds) exp)
      in if null neededPatBinds
         then match
         else Hsx.Match loc name pats rhs' binds
    where patBindNeeded patBind
              = not (Set.null ( Set.fromList (Hsx.extractBindingNs patBind)
                                `Set.intersection` Hsx.extractFreeVarNs exp ))
          boundNames = Set.fromList (Hsx.extractBindingNs pats)
          shadowPatBind :: Hsx.Decl () -> Hsx.Decl ()
          shadowPatBind (Hsx.PatBind loc pat rhs binds) 
              = (Hsx.PatBind loc (shadow pat) rhs binds) 
          shadowPVar :: Hsx.Pat () -> Hsx.Pat ()
          shadowPVar var@(Hsx.PVar _ name) 
              | Hsx.UnQual () name `Set.member` boundNames = Hsx.PWildCard ()
              | otherwise = var
          shadowPVar oth = oth 
                            
          shadow :: GenericT
          shadow = everywhere (mkT shadowPVar)

addPatBindsToDecl :: [Hsx.Decl ()] -> Hsx.Decl () -> Hsx.Decl ()
addPatBindsToDecl patBinds (Hsx.FunBind l matches) = 
    let matches' = map (addPatBindsToMatch patBinds) matches
    in Hsx.FunBind l matches'
addPatBindsToDecl _ decl@(Hsx.TypeSig _ _ _) = decl
addPatBindsToDecl patBinds decl = error $ "Function binding expected but found:\n" ++ Hsx.prettyPrint decl
     

delocaliseFunDefs :: [FunDef] -> DelocaliserM [Hsx.Decl ()]
delocaliseFunDefs funDefs = 
    do envNames <- Hsx.boundNames
       let freeNames = Set.unions (map funFreeNames funDefs)
           closureNames = freeNames `Set.intersection` envNames
           closureNameList = Set.toList closureNames
           closureUNameList = map uname closureNameList
           funNames = map funName funDefs
       renamings <- liftGensym $ Hsx.freshIdentifiers funNames
       envUName <- liftGensym $ Gensym.genHsName (Hsx.Ident () "env")
       let envName = Hsx.UnQual () envUName
           addEnv (orig,ren) = (orig, Hsx.App () (Hsx.Var () ren) (Hsx.Var () envName))
           envTuple = case closureNameList of
                        [closureName] -> Hsx.Var () closureName
                        _ -> Hsx.Tuple () Hsx.Boxed (map (Hsx.Var ()) closureNameList)
           patBind f (orig,ren) = Hsx.PatBind
                                    ()
                                    (Hsx.PVar () $ uname orig)
                                    (Hsx.UnGuardedRhs () $ f (Hsx.Var () ren))
                                    Nothing
           addEnvTuple = patBind (\x -> Hsx.App () x envTuple)
           withoutEnvTuple = patBind id
           subst = Map.fromList $ map addEnv renamings
           funs = map funBind funDefs
           funsRenamed = map (Hsx.renameDecl renamings) funs
           funsNoEnvPassing = map (Hsx.renameFreeVars renamings) funsRenamed
           funsEnvPassing = Hsx.applySubst subst funsRenamed
           funsDeloc = if null closureNameList 
                       then funsNoEnvPassing
                       else map (addEnvArgToDecl envUName closureUNameList) funsEnvPassing
           newPatBinds = if null closureNameList
                         then map withoutEnvTuple renamings
                         else map addEnvTuple renamings
       addTopDecls funsDeloc
       return newPatBinds
    where uname (Hsx.Qual _ _ name) = name
          uname (Hsx.UnQual _ name) = name

delocaliseLet :: Hsx.Exp () -> DelocaliserM (Hsx.Exp ())
delocaliseLet (Hsx.Let l binds exp) = 
    let (Hsx.BDecls _ patBinds, Hsx.BDecls _ funBinds) = splitPatBinds (checkBindings binds)
        funBinds' = map (addPatBindsToDecl patBinds) funBinds
        funDefs = funDefComponents (groupFunDefs funBinds') 
    in do newPatBinds <- mapM delocaliseFunDefs funDefs
          let newBinds = Hsx.BDecls () $ (concat newPatBinds) ++ patBinds
          return $ Hsx.Let l newBinds exp
delocaliseLet exp = return exp 



{-|
  This predicates checks whether the argument is a pattern binding.
-}
isPatBind :: Hsx.Decl () -> Bool
isPatBind (Hsx.PatBind _ _ _ _) = True
isPatBind _ = False


{-|
  This function partitions bindings into a pair (pattern bindings, other bindings)
-}
splitPatBinds :: Hsx.Binds () -> (Hsx.Binds (), Hsx.Binds ())
splitPatBinds (Hsx.BDecls _ decls) 
    = let (patDecls, typeSigs, otherDecls)    = unzip3 (map split decls)
          (patDecls', typeSigs', otherDecls') = (catMaybes patDecls, 
                                                 concatMap flattenTypeSig (catMaybes typeSigs), 
                                                 catMaybes otherDecls)
          (patTypeSigs, otherTypeSigs) 
              = partition (let patNs = concatMap Hsx.namesFromDeclInst patDecls'
                           in \sig -> head (Hsx.namesFromDeclInst sig) `elem` patNs)
                          typeSigs'
      in (Hsx.BDecls () (patTypeSigs ++ patDecls'), Hsx.BDecls () (otherTypeSigs ++ otherDecls'))

    where split decl@(Hsx.PatBind _ _ _ _) = (Just decl, Nothing, Nothing)
          split decl@(Hsx.TypeSig _ _ _) = (Nothing, Just decl, Nothing)
          split decl = (Nothing, Nothing, Just decl)
splitPatBinds junk = error ("splitPatBinds: Fall through. " ++ show junk)

getPatDecls :: Hsx.Binds () -> [Hsx.Decl ()]
getPatDecls bindings
    = let Hsx.BDecls _ patdecls = fst (splitPatBinds bindings) in patdecls

flattenTypeSig :: Hsx.Decl () -> [Hsx.Decl ()]
flattenTypeSig (Hsx.TypeSig loc names typ)
    = map (\n -> Hsx.TypeSig loc [n] typ) names

---- Normalization of names.
--
-- Function definitions are restricted in Isar/HOL such that names of
-- constants must not be used as a bound variable name in those definitions.
-- 
-- We simply rename all those identifiers.
--

should_be_renamed :: [String] -> Hsx.QName () -> Bool
should_be_renamed reserved qn = case qn of
                         Hsx.Qual _ _ n -> consider n
                         Hsx.UnQual _ n -> consider n
    where consider (Hsx.Ident _ s)  = s `elem` reserved
          consider (Hsx.Symbol _ s) = s `elem` reserved

normalizeNames_Decl :: [String] -> Hsx.Decl () -> Gensym.GensymM (Hsx.Decl ())
normalizeNames_Decl reserved (Hsx.FunBind l matchs)
    = do matchs' <- mapM normalizePatterns_Match matchs
         return (Hsx.FunBind l matchs')
    where
      normalizePatterns_Match (Hsx.Match loc name pats (Hsx.UnGuardedRhs loc' body) where_binds)
          = let bound_var_ns = Hsx.bindingsFromPats pats
                clashes      = filter (should_be_renamed reserved) bound_var_ns
            in do renames <- Hsx.freshIdentifiers clashes
                  pats'   <- return (map (Hsx.renamePat renames) pats)
                  body'   <- return (Hsx.renameFreeVars renames body)
                  binds'  <- mapM normalizeNames_Binds where_binds
                  return (Hsx.Match loc name pats' (Hsx.UnGuardedRhs loc' body') binds') 
      normalizePatterns_Match (Hsx.InfixMatch loc pat name pats (Hsx.UnGuardedRhs loc' body) where_binds)
          = do Hsx.Match loc name (pat : pats) body where_binds <- normalizePatterns_Match (Hsx.Match loc name (pat : pats) (Hsx.UnGuardedRhs loc' body) where_binds)
               return (Hsx.InfixMatch loc pat name pats body where_binds)

      normalizeNames_Binds (Hsx.BDecls loc decls)
          = do decls' <- mapM (normalizeNames_Decl reserved) decls
               return (Hsx.BDecls loc decls')

normalizeNames_Decl reserved decl
    -- There aren't any subdecls in decl anymore after delocalization.
    = return decl

-- normalizeModuleNameName :: String -> String


whereToLet :: Hsx.Decl () -> Hsx.Decl ()
whereToLet =
    everywhere $ mkT 
    whereToLetDecl `extT`
    whereToLetMatch `extT`
    whereToLetAlt

isEmptyBinds :: Maybe (Hsx.Binds ()) -> Bool
isEmptyBinds (Just (Hsx.BDecls _ [])) = True
isEmptyBinds (Just (Hsx.IPBinds _ [])) = True
isEmptyBinds Nothing = True
isEmptyBinds _ = False

whereToLetRhs _     (Hsx.GuardedRhss _ _) = assert False undefined
whereToLetRhs binds (Hsx.UnGuardedRhs _ exp) =
    Hsx.UnGuardedRhs () $ Hsx.Let () (case binds of Nothing -> Hsx.BDecls () [] ; Just binds -> binds) exp

whereToLetDecl :: Hsx.Decl () -> Hsx.Decl ()
whereToLetDecl (Hsx.PatBind loc pat rhs binds)
    | not $ isEmptyBinds binds = Hsx.PatBind loc pat (whereToLetRhs binds rhs) Nothing
whereToLetDecl decl = decl

whereToLetMatch :: Hsx.Match () -> Hsx.Match ()
whereToLetMatch match@(Hsx.Match loc name pats rhs binds)
    | isEmptyBinds binds = match
    | otherwise = Hsx.Match loc name pats (whereToLetRhs binds rhs) Nothing
whereToLetMatch match@(Hsx.InfixMatch loc pat name pats rhs binds)
    | isEmptyBinds binds = match
    | otherwise = Hsx.InfixMatch loc pat name pats (whereToLetRhs binds rhs) Nothing

whereToLetAlt :: Hsx.Alt () -> Hsx.Alt ()
whereToLetAlt orig@(Hsx.Alt loc pat alt binds) 
    | isEmptyBinds binds = orig
    | otherwise = Hsx.Alt loc pat (whereToLetRhs binds alt) Nothing


---- Deguardification

type DeguardifyEnv = Reader Bool

runDeguardifyEnv :: DeguardifyEnv a -> a
runDeguardifyEnv m = runReader m False

{-|
  This environment defines a Boolean value indicating whether we are inside
  the last match in a function definition
-}
deguardify :: forall l. (Eq l, Data l, Ord l, Show l) => Hsx.Decl l -> Hsx.Decl l
deguardify decl = runDeguardifyEnv $ everywhereEnv deguardifyEnv deguardifyLocal decl
    where
      deguardifyEnv :: (Monad m) => EnvDef m Bool
      deguardifyEnv = mkE fromMatches
      fromMatches :: [Hsx.Match l] -> Envs (Repl Bool)
      fromMatches [] = Envs []
      fromMatches [_] = Envs [Set True,Set False]
      fromMatches (_:_) = Envs [Set False,Set False]

      deguardifyLocal :: GenericM DeguardifyEnv
      deguardifyLocal = mkM (deguardifyRhs :: Hsx.Rhs () -> DeguardifyEnv (Hsx.Rhs ()))
                        `extM` (deguardifyAlts :: Hsx.Rhs () -> DeguardifyEnv (Hsx.Rhs ()))


deguardifyRhs :: Hsx.Rhs () -> DeguardifyEnv (Hsx.Rhs ())
deguardifyRhs rhs@(Hsx.UnGuardedRhs _ _) = return rhs
deguardifyRhs (Hsx.GuardedRhss _ guards) = liftM (Hsx.UnGuardedRhs ()) $ deguardifyGuards guards

deguardifyAlts :: Hsx.Rhs () -> DeguardifyEnv (Hsx.Rhs ())
deguardifyAlts alt@(Hsx.UnGuardedRhs _ _) = return alt
deguardifyAlts (Hsx.GuardedRhss _ guards) = 
    liftM (Hsx.UnGuardedRhs ()) .
    deguardifyGuards .
    (map (\(Hsx.GuardedRhs l ss e) -> Hsx.GuardedRhs l ss e)) $
    guards
deguardifyGuards :: [Hsx.GuardedRhs ()] -> DeguardifyEnv (Hsx.Exp ())
deguardifyGuards guards = 
    do isLast <- ask
       let findOtherwiseExpr guards
               = case break isTrivial guards of
                   (guards', (Hsx.GuardedRhs _ _ last_expr):_) -> (guards', last_expr)
                   (guards',[])
                       | isLast -> let Hsx.GuardedRhs srcLoc _ _ = last guards'
                                   in error $ show {-Msg.found_inconsistency_in_guards-} srcLoc
                       | otherwise -> (guards', bottom)
           (guards', otherwise_expr) = findOtherwiseExpr guards
       return $ foldr deguardify otherwise_expr guards'
    where otherwise_stmt = Hsx.Qualifier () (Hsx.Var () (Hsx.UnQual () (Hsx.Ident () "otherwise")))
          true_stmt      = Hsx.Qualifier () (Hsx.Var () (Hsx.UnQual () (Hsx.Ident () "True")))
          bottom         = Hsx.Var () (Hsx.Qual () (Hsx.ModuleName () "Prelude") (Hsx.Symbol () "_|_")) 
          isTrivial (Hsx.GuardedRhs _ stmts _) =
              stmts `elem` [[otherwise_stmt], [true_stmt]]
          deguardify x@(Hsx.GuardedRhs loc stmts clause) body
              = Hsx.If () (makeGuardExpr stmts) clause body
          makeGuardExpr stmts = if null stmts
                                then (Hsx.Var () (Hsx.UnQual () (Hsx.Ident () "True")))
                                else foldl1 andify (map expify stmts)
              where expify (Hsx.Qualifier _ exp) = exp
                    andify e1 e2 = Hsx.InfixApp () e1 (Hsx.QVarOp () (Hsx.Qual () (Hsx.ModuleName () "Prelude") (Hsx.Symbol () "&&"))) e2


-- `let' in Haskell is actually a letrec, but Isar/HOL does not allow
-- recursive let expressions. We hence check the bindings in question
-- whether or not we can deal with them.
--
checkBindings :: Hsx.Binds () -> Hsx.Binds ()
checkBindings bindings
    = checkForRecursiveBinds . checkForForwardRefs $ bindings

-- Check for forward references, e.g. prohibit
--
--    let a = b * 42 
--        b = 23 in ... 
-- 
-- as `b' is referenced before its binding is established.
--
-- Notice that do allow forward referencing to functions like for
-- instance in
--
--    let a x = 32 + b x
--        b y = c (- y)
--        c z = 42 * z in ...
-- 
-- We can allow this because the function will be globalized, and
-- hence moved out of the `let' expression.
--
checkForForwardRefs bindings
    = let vardecls = getPatDecls bindings
      in case filter (\(decl, forwardNss) 
                          -> any (`elem` concat forwardNss) $ Set.toList (Hsx.extractFreeVarNs decl))
                $ zip vardecls
                      -- These are the consecutively following binding names:
                      (tails (map Hsx.extractBindingNs vardecls))
      of []          -> bindings
         (decl, _):_ -> error (Msg.forward_bindings_disallowed (Hsx.getSrcLoc decl))

-- Check for recursive binding attempts, e.g. prohibit
--
--    let ones = 1 : ones in ...
--
-- For the same reasons as above (forward refs), we do all recursive
-- local function definitions.
--
checkForRecursiveBinds bindings
    = let find_recursive_binds = filter (\d -> any (`elem` Hsx.extractBindingNs d) 
                                                 $ Hsx.extractVarNs d)
      in case find_recursive_binds (getPatDecls bindings) of
        []  -> bindings
        d:_ -> error (Msg.recursive_bindings_disallowed (Hsx.getSrcLoc d))
