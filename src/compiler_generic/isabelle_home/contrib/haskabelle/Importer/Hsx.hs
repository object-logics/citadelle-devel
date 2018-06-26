{-# LANGUAGE
  UndecidableInstances,
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  Rank2Types #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen

Haskell ASTs.
-}

module Importer.Hsx where

import Importer.Library
import qualified Importer.AList as AList
import Data.Maybe
import Data.List (sort, sortBy)
import Data.Map (Map)
import qualified Data.Map as Map hiding (Map)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
import qualified Data.Array as Array (inRange)
import qualified Data.Char as Char (toLower)

import Data.Generics
import Data.Generics.Basics
import Data.Generics.Uniplate.Data

import Control.Monad.Reader

import qualified Importer.Gensym as Gensym
import qualified Importer.Env as Env

import qualified Language.Haskell.Exts as Hsx
import qualified Language.Haskell.Exts.SrcLoc as HsxL


type SLoc l = Maybe l

fmapNone :: (Eq l, Data l, Ord l, Show l) => Functor m => m a -> m (SLoc l)
fmapNone = fmap (\_ -> Nothing)

fmapJust :: (Eq l, Data l, Ord l, Show l) => Functor m => m l -> m (SLoc l)
fmapJust = fmap Just

fmapUnit :: Functor m => m a -> m ()
fmapUnit = fmap (\_ -> ())

{-|
  The prelude's module name
-}
hsk_prelude :: Hsx.ModuleName ()
hsk_prelude = Hsx.ModuleName () "Prelude"

zipMod0 :: (a -> Hsx.Module l) -> [a] -> [(Hsx.ModuleName (), a)]
zipMod0 f = map (\(modulN, modul) ->
               ( case f modul of Hsx.Module _ (Just (Hsx.ModuleHead _ m _ _)) _ _ _ -> fmapUnit m
                                 _ -> Hsx.ModuleName () (show modulN)
               , modul))
          . zip [0..]

zipMod :: [Hsx.Module l] -> [(Hsx.ModuleName (), Hsx.Module l)]
zipMod = zipMod0 id

{-|
  This function takes a constant identifier name and converts it into a
  Haskell expression of a qualified 
-}
prelude_fn :: String -> Hsx.Exp ()
prelude_fn fn_name = Hsx.Var () (Hsx.Qual () hsk_prelude (Hsx.Ident () fn_name))

{-|
  This function provides the return type of a type. E.g.
  returnType (a -> b -> c) = c
-}
returnType :: Hsx.Type () -> Hsx.Type ()
returnType (Hsx.TyForall _ _ _ ty) = ty
returnType (Hsx.TyFun _ _ ty) = ty
returnType (Hsx.TyKind _ ty _) = ty
returnType ty = ty


{-|
  This function provides the (unqualified) name of the type constructor that constructed
  the given type or nothing if the given type is not a constructor application.
-}
typeConName :: Hsx.Type () -> Maybe String
typeConName (Hsx.TyApp _ (Hsx.TyCon _ qname) _) =
    case qname of
      Hsx.Qual _ _ (Hsx.Ident _ name) -> Just name
      Hsx.UnQual _ (Hsx.Ident _ name) -> Just name
      _                     -> Nothing
typeConName _ = Nothing


isHskSymbol :: Char -> Bool
isHskSymbol = flip elem ['_', ':', '"', '[', ']', '!', '#', '$', '%', '&',
                         '*', '+', '.', '/', '<', '=', '>', '?', '@',
                         '\\', '^', '|', '-', '~' ]

isOperator :: String -> Bool
isOperator = all isHskSymbol

{-|
  This function takes a Haskell expression and applies it to the argument
  given in the list
-}
hsk_apply :: Hsx.Exp () -> [Hsx.Exp ()] -> Hsx.Exp ()
hsk_apply fn_expr args
    = foldl (Hsx.App ()) fn_expr args

{-|
  The Haskell empty list.
-}
hskPNil :: Hsx.Pat ()
hskPNil = Hsx.PList () []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hskPCons :: Hsx.Pat () -> Hsx.Pat () -> Hsx.Pat ()
hskPCons x y = Hsx.PApp () (Hsx.Special () (Hsx.Cons ())) [x, y]

{-|
  The Haskell empty list.
-}
hsk_nil :: Hsx.Exp ()
hsk_nil             = Hsx.List () []

{-|
  The Haskell list constructor. This function takes two Haskell expressions and applies
  the list constructor @(:)@ to it.
-}
hsk_cons :: Hsx.Exp () -> Hsx.Exp () -> Hsx.Exp ()
hsk_cons x y        = Hsx.App () (Hsx.App () (Hsx.Con () (Hsx.Special () (Hsx.Cons ()))) x) y

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hskPPair :: Hsx.Pat () -> Hsx.Pat () -> Hsx.Pat ()
hskPPair x y = Hsx.PApp () (Hsx.Special () (Hsx.TupleCon () Hsx.Boxed 2)) [x, y]

{-|
  The Haskell pair constructor. This function takes two Haskell expressions and applies
  the pair constructor @(,)@ to them.
-}
hsk_pair :: Hsx.Exp () -> Hsx.Exp () -> Hsx.Exp ()
hsk_pair x y        = Hsx.App () (Hsx.App () (Hsx.Con () (Hsx.Special () (Hsx.TupleCon () Hsx.Boxed 2))) x) y

{-|
  The Haskell logical negation. This function takes a Haskell expression and applies
  the negation 'negate' to it.
-}
hsk_negate :: Hsx.Exp () -> Hsx.Exp ()
hsk_negate e        = hsk_apply (prelude_fn "negate") [e]

{-|
  The Haskell if-then-else. This function takes three arguments - condition, if branch, else branch -
  and forms a corresponding if-then-else expression.
-}
hsk_if ::  Hsx.Exp () -> Hsx.Exp () -> Hsx.Exp () -> Hsx.Exp ()
hsk_if = Hsx.If ()

{-|
  The Haskell lambda abstraction.
-}
hsk_lambda :: [Hsx.Pat ()] -> Hsx.Exp () -> Hsx.Exp ()
hsk_lambda = Hsx.Lambda ()

{-|
  The Haskell (ungarded!) case expression.
-}
hsk_case :: Hsx.Exp () -> [(Hsx.Pat (), Hsx.Exp ())] -> Hsx.Exp ()
hsk_case e cases
    = Hsx.Case () e [ Hsx.Alt () pat (Hsx.UnGuardedRhs () exp) Nothing | (pat, exp) <- cases ]

{-|
  This function turns a string into a Haskell name. Depending on the
  actual string it is considered a symbol (cf. 'Hsx.Symbol') or an
  identifier (cf. 'Hsx.Ident').
-}
string2Name :: String -> Hsx.Name ()
string2Name string = case isSymbol string of
                         True  -> Hsx.Symbol () string
                         False -> Hsx.Ident () string
    where isSymbol string = and $ map (`elem` symbols) string
          symbols = "!@$%&*+./<=>?¹\\^|~"

{-|
  This function turns a source location into a human readable string.
-}
srcloc2string :: Hsx.SrcLoc -> String
srcloc2string (Hsx.SrcLoc { Hsx.srcFilename=filename, Hsx.srcLine=line, Hsx.srcColumn=column })
    = filename ++ ":" ++ (show line) ++ ":" ++ (show column)

srcspan2string :: HsxL.SrcSpan -> String
srcspan2string (HsxL.SrcSpan { HsxL.srcSpanFilename=filename, HsxL.srcSpanStartLine=line1, HsxL.srcSpanStartColumn=column1, HsxL.srcSpanEndLine=line2, HsxL.srcSpanEndColumn=column2 })
    = "(" ++ srcloc2string (Hsx.SrcLoc { Hsx.srcFilename=filename, Hsx.srcLine=line1, Hsx.srcColumn=column1 })
          ++ ", "
          ++ srcloc2string (Hsx.SrcLoc { Hsx.srcFilename=filename, Hsx.srcLine=line2, Hsx.srcColumn=column2 })
          ++ ")"

{-|
  This function computes the relative file path to the given module name.
  E.g.  \"Some.Hsx.ModuleName.Name\" ==> \"Some\/Hsx.ModuleName\/Name\"
-}
module2FilePath :: Hsx.ModuleName () -> FilePath
module2FilePath (Hsx.ModuleName _ name)
    = map (\c -> if c == '.' then '/' else c) name ++ ".hs"
{-
moduleFileLocation :: Hsx.Module () -> FilePath
moduleFileLocation (Hsx.Module Hsx.SrcLoc{Hsx.srcFilename = file} _ _ _ _) = file
-}
moduleHierarchyDepth :: Hsx.ModuleName () -> Int
moduleHierarchyDepth (Hsx.ModuleName _ name) = length $ filter (== '.') name

{-|
  This predicate checks whether the given file path refers to a Haskell
  source file.
-}
isHaskellSourceFile :: FilePath -> Bool
isHaskellSourceFile fp = map Char.toLower (last (slice (== '.') fp)) == "hs"

{-|
  This function takes a context (from a class definition) and extracts
  the super classes' names.

  TODO: This is to specific: Contexts can be more complex. This function only returns
  the \"super classes\" if the context's assertion have the class' type variable as their
  only argument. Also other kinds of assertions are not considered.
-}
extractSuperclassNs' :: [Hsx.Asst ()] -> [Hsx.QName ()]
extractSuperclassNs' ctx = map extract ctx
    where extract (Hsx.ClassA _ qn _) = qn
          extract (Hsx.ParenA _ a) = extract a

extractSuperclassNs :: Maybe (Hsx.Context ()) -> [Hsx.QName ()]
extractSuperclassNs = extractSuperclassNs' . (\x -> case x of Nothing -> []
                                                              Just l -> contextList l)

contextList :: Hsx.Context () -> [Hsx.Asst ()]
contextList (Hsx.CxSingle _ a) = [a]
contextList (Hsx.CxTuple _ la) = la
contextList (Hsx.CxEmpty _) = []

dest_typcontext :: Hsx.Context () -> [(Hsx.Name (), [Hsx.QName ()])]
dest_typcontext ctx = AList.group (maps dest_entry $ contextList ctx) where
  dest_entry (Hsx.ClassA _ cls typs) = [ (v, cls) | v <- map dest_tyvar typs ]
  dest_entry (Hsx.ParenA _ a) = dest_entry a
  dest_tyvar (Hsx.TyVar _ v) = v

{-|
  This function extracts the type declarations of the given list of
  class-internal declarations.
-}
extractMethodSigs :: Maybe [Hsx.ClassDecl ()] -> [Hsx.Decl ()]
extractMethodSigs class_decls
    = filter isTypeSig (map (\(Hsx.ClsDecl _ d) -> d) (case class_decls of Nothing -> [] ; Just l -> l))
    where isTypeSig (Hsx.TypeSig _ _ _) = True
          isTypeSig _                   = False

{-|
  This function extracts all Haskell names that are affected by the given
  declaration. If the given kind of declaration is not supported an exception
  is thrown.
-}
namesFromDecl :: Hsx.Decl () -> Either [Hsx.QName ()] (Hsx.QName ())
namesFromDecl decl = case decl of
    Hsx.TypeDecl _ name _        -> namesFromDeclHead name
    Hsx.DataDecl _ _ _ name _ _  -> namesFromDeclHead name
    Hsx.ClassDecl _ _ name _ _   -> namesFromDeclHead name
    Hsx.InstDecl _ _ irule _     -> namesFromInstRule irule
    Hsx.TypeSig _ names _        -> Left $ map (Hsx.UnQual ()) names
    Hsx.InfixDecl _ _ _ ops      -> Left [Hsx.UnQual () n | n <- (universeBi ops :: Data l => [Hsx.Name l])]
    Hsx.PatBind _ pat _ _        -> Left $ bindingsFromPats [pat]
    Hsx.FunBind _ (Hsx.Match _ fname _ _ _ : ms )
                                 -> Left [Hsx.UnQual () fname]
    Hsx.FunBind _ (Hsx.InfixMatch _ _ fname _ _ _ : ms )
                                 -> Left [Hsx.UnQual () fname]
    decl                         -> error $ "Internal error: The given declaration " ++ show decl ++ " is not supported!"
  where
    namesFromDeclHead name = Left [(Hsx.UnQual () . fst . split_declhead) name]
    namesFromInstRule (Hsx.IRule _ _ _ ihead) = Right ((fst . split_insthead) ihead)

namesFromDeclInst :: Hsx.Decl () -> [Hsx.QName ()]
namesFromDeclInst decl = case namesFromDecl decl of Left l -> l ; Right n -> [n]

namesFromDecl' :: Hsx.Decl () -> [Hsx.QName ()]
namesFromDecl' decl = case namesFromDecl decl of Left l -> l ; Right _ -> []

split_declhead :: Hsx.DeclHead l -> (Hsx.Name l, [Hsx.TyVarBind l])
split_declhead dh = case dh of Hsx.DHead _ n -> (n, [])
                               Hsx.DHInfix _ t n -> (n, [t])
                               Hsx.DHParen _ dh -> split_declhead dh
                               Hsx.DHApp _ dh t -> let (n, l) = split_declhead dh in (n, l ++ [t])

split_insthead :: Hsx.InstHead l -> (Hsx.QName l, [Hsx.Type l])
split_insthead dh = case dh of Hsx.IHCon _ n -> (n, [])
                               Hsx.IHInfix _ t n -> (n, [t])
                               Hsx.IHParen _ dh -> split_insthead dh
                               Hsx.IHApp _ dh t -> let (n, l) = split_insthead dh in (n, l ++ [t])

{-|
  Instances of this class represent pieces of Haskell syntax that can bind 
  variables.
-}

class HasBindings a where
    {-|
      This function is supposed to provide a list of all Haskell variables that
      are bound by the given syntax.
     -}
    extractBindingNs :: a -> [Hsx.QName ()]

{-|
  Lift all instances to lists.
-}
instance HasBindings a => HasBindings [a] where
    extractBindingNs list = concatMap extractBindingNs list

instance HasBindings (Hsx.Pat ()) where
    extractBindingNs pattern = bindingsFromPats [pattern]

instance HasBindings (Hsx.Decl ()) where
    extractBindingNs decl = bindingsFromDecls [decl] 

instance HasBindings (Hsx.Binds ()) where
    extractBindingNs (Hsx.BDecls _ decls) = extractBindingNs decls
    extractBindingNs (Hsx.IPBinds _ (Hsx.IPBind loc _ _ : _))
        = error $ show {-srcloc2string-} loc ++ ": Implicit parameter bindings are not supported!"
    extractBindingNs (Hsx.IPBinds _ []) = []

instance HasBindings (Maybe (Hsx.Binds ())) where
    extractBindingNs (Just b) = extractBindingNs b
    extractBindingNs Nothing  = []

instance HasBindings (Hsx.Stmt ()) where
    extractBindingNs (Hsx.Qualifier _ b)         = []
    extractBindingNs (Hsx.Generator _ pat exp) = extractBindingNs pat
    extractBindingNs (Hsx.LetStmt _ binds)       = extractBindingNs binds

instance HasBindings (Hsx.QualStmt ()) where
    extractBindingNs (Hsx.QualStmt _ stmt) = extractBindingNs stmt
    extractBindingNs _                   = []


{-|
  This function extracts from the given Haskell pattern a list of all Haskell variables
  that are bound by the pattern.
-}
bindingsFromPats          :: [Hsx.Pat ()] -> [Hsx.QName ()]
bindingsFromPats pattern  = [ Hsx.UnQual l n | Hsx.PVar l n <- universeBi pattern ]
                            ++ [ Hsx.UnQual l n | Hsx.PAsPat l n _ <- universeBi pattern ]

{-|
  This function extracts the variables bound by the given declaration.
-}
bindingsFromDecls       :: [Hsx.Decl ()] -> [Hsx.QName ()]
bindingsFromDecls decls = assert (not (has_duplicates bindings)) bindings
    -- Type signatures do not create new bindings, but simply annotate them.
    where bindings = concatMap namesFromDeclInst (filter (not . isTypeSig) decls)
          isTypeSig (Hsx.TypeSig _ _ _) = True
          isTypeSig _                 = False


type HskNames = Set (Hsx.QName ())
newtype BindingM a = BindingM (Reader HskNames a)
    deriving (Monad, MonadReader HskNames, Functor, Applicative)

runBindingM :: BindingM a -> a
runBindingM (BindingM m) = runReader m Set.empty

class BindingMonad m where
    boundNames :: m HskNames
    isBound :: Hsx.QName () -> m Bool
    

instance MonadReader HskNames m => BindingMonad m where
    isBound name = ask >>=  (return . Set.member name)
    boundNames = ask

type Subst = Map (Hsx.QName ()) (Hsx.Exp ())

{-|
  This function extracts the set of the names that are bound by
  the given piece of Haskell Syntax.
-}

boundNamesEnv :: Monad m => Env.EnvDef m HskNames
boundNamesEnv = Env.mkE fromExp
             `Env.extE` fromAlt
             `Env.extE` fromDecl
             `Env.extE` fromMatch
             `Env.extE` fromStmts
    where fromExp :: Hsx.Exp () -> Env.Envs HskNames
          fromExp (Hsx.Let _ binds _)
              = let bound = Set.fromList $ extractBindingNs binds
                in Env.Envs [bound, bound, bound]
          fromExp (Hsx.Lambda _ pats _)
              = let bound = Set.fromList $ extractBindingNs pats
                in Env.Envs [Set.empty, bound, bound]
          fromExp (Hsx.MDo _ stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in Env.Envs [bound]
          fromExp (Hsx.ListComp _ _ stmts)
              = let bound = Set.fromList $ extractBindingNs stmts
                in Env.Envs [bound, bound, bound]
          fromExp exp = Env.uniEloc exp Set.empty
                            
          fromAlt :: Hsx.Alt () -> HskNames
          fromAlt (Hsx.Alt _ pat _ _) = Set.fromList $ extractBindingNs pat

          fromDecl :: Hsx.Decl () -> HskNames
          fromDecl (Hsx.PatBind _ _ _ whereBinds) = Set.fromList $
                                                       extractBindingNs whereBinds
          fromDecl _ = Set.empty

          fromMatch :: Hsx.Match () -> HskNames
          fromMatch (Hsx.Match _ _ pats _ whereBinds)
              = Set.fromList $ 
                extractBindingNs whereBinds ++ extractBindingNs pats
          fromMatch (Hsx.InfixMatch _ pat _ pats _ whereBinds)
              = Set.fromList $ 
                extractBindingNs whereBinds ++ extractBindingNs pat ++ extractBindingNs pats

          fromStmts :: [Hsx.Stmt ()] -> Env.Envs HskNames
          fromStmts [] = Env.Envs []
          fromStmts (Hsx.Generator loc pat exp : _)
              = let bound = Set.fromList $ extractBindingNs pat
                in Env.Envs [Set.empty, bound]
          fromStmts (Hsx.Qualifier _ _ : _)
              = Env.Envs [Set.empty, Set.empty]
          fromStmts (Hsx.LetStmt _ binds : _)
              = let bound = Set.fromList $ extractBindingNs binds
                in Env.Envs [bound, bound]

{-|
  This is a monadic query function that returns
  if the argument is a free name a singleton set
  containing that name and otherwise an empty set.
-}
freeNamesLocal :: GenericQ (BindingM HskNames)
freeNamesLocal hs = case name hs of
                Nothing -> return Set.empty
                Just name ->
                    do bound <- isBound name
                       if bound
                         then return Set.empty
                         else return (Set.singleton name)
    where name = mkQ Nothing fromExp
                  `extQ`fromQOp
          fromExp (Hsx.Var _ name) = Just name
          fromExp _ = Nothing
                      
          fromQOp (Hsx.QVarOp _ name) = Just name
          fromQOp _ = Nothing


{-|
  This function extracts names that are implicitly declared, such as data constructors
  and record fields.
-}
extractImplDeclNs :: Hsx.Decl () -> HskNames
extractImplDeclNs decl@(Hsx.DataDecl _ _ _ _ _ _) =
    everything Set.union (mkQ Set.empty fromConDecl) decl
    where fromConDecl (Hsx.ConDecl _ name _) = Set.singleton (Hsx.UnQual () name)
          fromConDecl (Hsx.RecDecl _ name fields) = 
              Set.singleton (Hsx.UnQual () name) 
                     `Set.union` Set.fromList (map (Hsx.UnQual ()) (concatMap (\(Hsx.FieldDecl _ ln _) -> ln) fields))

extractImplDeclNs _ = Set.empty

{-|
  This function extracts the names of data constructors used
  in patters from the given piece of Haskell syntax.
-}

extractDataConNs :: Data a => a -> HskNames
extractDataConNs = everything Set.union (mkQ Set.empty fromPat)
    where fromPat (Hsx.PApp _ name _) = Set.singleton name
          fromPat (Hsx.PRec _ name _) = Set.singleton name
          fromPat (Hsx.PInfixApp _ _ name _) = Set.singleton name
          fromPat _ = Set.empty

{-|
  This function extracts the names of type constructors in the given piece of
  Haskell syntax
-}
extractTypeConNs :: Data a => a -> HskNames
extractTypeConNs = everything Set.union (mkQ Set.empty fromType `extQ` fromAsst) where
  fromType (Hsx.TyCon _ name) = Set.singleton name
  fromType (Hsx.TyVar _ _) = Set.empty
  fromType (Hsx.TyTuple _ Hsx.Boxed typs) = Set.unions (map fromType typs)
  fromType (Hsx.TyFun _ typ1 typ2) = Set.union (fromType typ1) (fromType typ2)
  fromType (Hsx.TyForall _ _ _ typ)  = fromType typ
  fromType (Hsx.TyApp _ typ1 typ2) = Set.union (fromType typ1) (fromType typ2)
  fromType (Hsx.TyParen _ typ) = fromType typ
  fromType (Hsx.TyList _ typ) = fromType (Hsx.TyApp () (Hsx.TyCon () (Hsx.Special () (Hsx.ListCon ()))) typ)
  fromType (Hsx.TyBang _ _ _ typ) = fromType typ
  fromType typ = error ("extractTypeConNs: bad type " ++ show typ)
  fromAsst :: Hsx.Asst () -> HskNames
  fromAsst (Hsx.ClassA _ name _) = Set.singleton name
  fromAsst (Hsx.ParenA _ ass) = fromAsst ass
  fromAsst ass = error ("extractTypeConNs: bad asst " ++ show ass)

{-|
  This function returns the set of names of free variables
  in the given piece of Haskell syntax.
-}
extractFreeVarNs :: Data a => a -> HskNames
extractFreeVarNs = runBindingM . Env.everythingEnv boundNamesEnv Set.union freeNamesLocal

{-|
  This function extracts all used field labels
-}
extractFieldNs :: Data a => a -> HskNames
extractFieldNs = everything Set.union (mkQ Set.empty fromPat `extQ` fromExp)
    where fromPat (Hsx.PFieldPat _ field _) = Set.singleton field
          fromExp (Hsx.FieldUpdate _ field _) = Set.singleton field

applySubst :: Subst -> GenericT
applySubst subst = runBindingM . Env.everywhereEnv boundNamesEnv (applySubstLocal subst)

applySubstLocal :: Subst -> GenericM BindingM
applySubstLocal subst node =
    do bound <- boundNames
       let apply = mkT applyExp

           applyExp exp@(Hsx.Var _ name)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> new
           applyExp exp@(Hsx.InfixApp _ exp1 (Hsx.QVarOp _ name) exp2)
               = case doSubst name of
                   Nothing -> exp
                   Just new -> Hsx.App () (Hsx.App () new exp1) exp2
           applyExp exp@(Hsx.LeftSection _ exp' (Hsx.QVarOp _ name))
               = case doSubst name of
                   Nothing -> exp
                   Just new -> Hsx.App () new exp'
           applyExp exp@(Hsx.RightSection _ (Hsx.QVarOp _ name) exp')
               = case doSubst name of
                   Nothing -> exp
                   Just new -> Hsx.App () (Hsx.App () (Hsx.Var () (Hsx.UnQual () (Hsx.Ident () "flip"))) new) exp'
           applyExp exp = exp

           doSubst' name
                 | name `Set.member` bound
                     = Nothing
                 | otherwise
                     = Map.lookup name subst
           doSubst = doSubst'
       return (apply node)

renameFreeVarsLocal :: [Renaming] -> GenericM BindingM
renameFreeVarsLocal renamings node =
    do bound <- boundNames
       let apply = mkT applyExp
                   `extT` applyQOp

           applyExp (Hsx.Var l name) = Hsx.Var l (ren name)
           applyExp exp = exp
                      
           applyQOp (Hsx.QVarOp l name) = Hsx.QVarOp l (ren name)
           applyQOp qop = qop

           ren' name
                 | name `Set.member` bound
                     = name
                 | otherwise
                     = fromMaybe name (lookup name renamings)
           ren = ren'
       return (apply node)

renameFreeVars :: Data a => [Renaming] -> a -> a
renameFreeVars renamings node = runBindingM $ Env.everywhereEnv boundNamesEnv (renameFreeVarsLocal renamings) node

{-|
  This type is used to describe renamings of variables.
-}
type Renaming = (Hsx.QName (), Hsx.QName ())

{-|
  This function generates renamings for all variables given in the
  list to provide fresh names.
-}
freshIdentifiers :: [Hsx.QName ()] -> Gensym.GensymM [Renaming]
freshIdentifiers qnames
    = do freshs <- mapM Gensym.genHsQName qnames
         return (zip qnames freshs)

{-|
  This function takes a list of variables (which are supposed to be bound) and a renaming
  and reduces this renaming such that it does not affect bound variables.
-}
shadow :: [Hsx.QName ()] -> [Renaming] -> [Renaming]
shadow boundNs renamings  = filter ((`notElem` boundNs) . fst) renamings

{-|
  This function applies the given renaming to the given variable.
-}
qtranslate :: [Renaming] -> Hsx.QName () -> Hsx.QName ()
qtranslate renamings qname 
    = fromMaybe qname (lookup qname renamings)

{-|
  This function applies the given renaming to the given unqualified variable.
-}
translate :: [Renaming] -> Hsx.Name () -> Hsx.Name ()
translate renamings name 
    = let (Hsx.UnQual _ name') = qtranslate renamings (Hsx.UnQual () name) in name'

{-|
  This function applies the given renaming to all variables in the given
  pattern.
-}
renamePat :: [Renaming] -> Hsx.Pat () -> Hsx.Pat ()
renamePat renams pat
    = case pat of
        Hsx.PVar l name                 -> Hsx.PVar l (translate renams name)
        Hsx.PLit l s lit                -> Hsx.PLit l s lit
        Hsx.PInfixApp l pat1 qname pat2 -> Hsx.PInfixApp l pat1' qname' pat2'
            where pat1'  = renamePat renams pat1 
                  qname' = qtranslate renams qname
                  pat2'  = renamePat renams pat2
        Hsx.PApp l qname pats           -> Hsx.PApp l qname' pats'
            where qname' = qtranslate renams qname
                  pats'  = map (renamePat renams) pats
        Hsx.PTuple l b pats             -> Hsx.PTuple l b (map (renamePat renams) pats)
        Hsx.PList l pats                -> Hsx.PList l (map (renamePat renams) pats)
        Hsx.PParen l pat                -> Hsx.PParen l (renamePat renams pat)
        Hsx.PWildCard l                 -> Hsx.PWildCard l
        Hsx.PAsPat l name pat'          -> Hsx.PAsPat l (translate renams name) (renamePat renams pat')
        Hsx.PRec l name fields          -> Hsx.PRec l name fields'
                                       where fields' = map ren fields
                                             ren (Hsx.PFieldPat l n p) = Hsx.PFieldPat l n (renamePat renams p)
        _ -> error ("rename.Pat: Fall through: " ++ show pat)

{-|
  This function applies the given renaming to names bound by the given
  Haskell declaration (only type signatures, function and pattern bindings
  are affected).
-}
renameDecl :: [Renaming] -> Hsx.Decl () -> Hsx.Decl ()
renameDecl renamings decl = 
    case decl of
      Hsx.TypeSig l names typ
          -> Hsx.TypeSig l (map (translate renamings) names) typ
      Hsx.FunBind l matches
          -> Hsx.FunBind l (map renMatch matches)
      Hsx.PatBind l pat rhs binds 
          -> Hsx.PatBind l (renamePat renamings pat) rhs binds
      _ -> decl
    where renMatch (Hsx.Match l name pats rhs binds)
                   = Hsx.Match l (translate renamings name) pats rhs binds
extractVarNs thing
    = let varNs   = [ qn | Hsx.Var _ qn <- universeBi thing ]
          varopNs = [ qn | Hsx.QVarOp _ qn <- universeBi thing ] 
                    ++ [ qn | Hsx.QConOp _ qn <- universeBi thing ]
      in varNs ++ varopNs

{-|
  This function compares the two given declarations w.r.t. the 
  source location.
-}
orderDeclsBySourceLine :: (Int, a) -> (Int, a) -> Ordering
orderDeclsBySourceLine (decl1, _) (decl2, _) = compare decl1 decl2

getSrcLoc :: Hsx.Decl () -> Hsx.SrcLoc
getSrcLoc decl
    = head . sortBy compareLines $ (childrenBi decl :: [Hsx.SrcLoc])
    where compareLines loc1 loc2 
              = compare (Hsx.srcLine loc1) (Hsx.srcLine loc2)


{-|
  This function provides the source line where the given
  declaration is made.
-}
getSourceLine :: Hsx.Decl () -> Int
getSourceLine decl
    = let srclocs = childrenBi decl :: [Hsx.SrcLoc]
          lines   = map Hsx.srcLine srclocs
      in head (sort lines)

showModuleName :: Hsx.ModuleName () -> String
showModuleName (Hsx.ModuleName _ name) = name


flattenRecFields :: [Hsx.FieldDecl ()] -> [(Hsx.Name (),Hsx.Type ())]
flattenRecFields = concatMap flatten
    where flatten (Hsx.FieldDecl _ ns bType) = zip ns (replicate (length ns) bType)
