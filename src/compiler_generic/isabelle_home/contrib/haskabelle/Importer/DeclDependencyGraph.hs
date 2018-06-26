{-# LANGUAGE FlexibleContexts #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen
-}

module Importer.DeclDependencyGraph 
    (arrangeDecls) where

import Importer.Library

import Data.Maybe
import qualified Data.List as List
import Data.Function
import Data.Graph as Graph
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
import Data.Traversable
import qualified Data.Tree as Tree

import Control.Monad

import qualified Importer.Msg as Msg
import qualified Importer.Ident_Env as Ident_Env

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Hsx as Hsx


-- We have to canonicalize the names in our graph, as there may appear
-- "some_fun", and "Foo.some_fun", and they may be reffering to the
-- same. We use our GlobalEnv for this purpose.

{-|
  This data structure represents the dependency graph of Haskell declarations.
  The nodes of this graph are elements of type 'Hsx.Decl' keys are of type 'Ident_Env.Name'.
-}
type HskDecl = (Int, Hsx.Decl ())
type HskDeclDepGraphKey = (Maybe Int, Ident_Env.Name)
data HskDeclDepGraph = HskDeclDepGraph (Graph, 
                                        Vertex -> (HskDecl, HskDeclDepGraphKey, [HskDeclDepGraphKey]), 
                                        HskDeclDepGraphKey -> Maybe Vertex)

{-|
  This function computes the dependency graph of the given Haskell declarations of the
  given module in the given environment. An edge from a declaration A to declaration B
  means the definition of A depends on B.
-}
makeDeclDepGraph :: Bool -> Ident_Env.GlobalE -> Hsx.ModuleName () -> [Hsx.Decl ()] -> HskDeclDepGraph
makeDeclDepGraph ignoreNotInScope globalEnv modul decls = HskDeclDepGraph declDepGraph
    where declDepGraph = graphFromEdges
                           $ handleDuplicateEdges
                               $ concatMap (makeEdgesFromDecl ignoreNotInScope globalEnv modul) (zip [0..] decls)

{-|
  This function constructs the outgoing edges of the given declaration in the given environment
  module.
-}
makeEdgesFromDecl :: Bool -> Ident_Env.GlobalE -> Hsx.ModuleName () -> HskDecl -> [(HskDecl, Ident_Env.Name, [Ident_Env.Name])]
makeEdgesFromDecl ignoreNotInScope globalEnv modul (pos, decl) =
  let
    canonicalize hsqname = Ident_Env.resolveName_OrLose globalEnv (Ident_Env.fromHsk modul) (Ident_Env.fromHsk hsqname)
    canonicalize' =
      if ignoreNotInScope then
        \hsqname -> let hsqname' = Ident_Env.fromHsk hsqname in
                    maybe hsqname' id (Ident_Env.resolveName_NoLose globalEnv (Ident_Env.fromHsk modul) hsqname')
      else
        canonicalize
    names = map canonicalize $ Hsx.namesFromDeclInst decl
    used_names = Set.map canonicalize' $ Set.unions [Hsx.extractFreeVarNs decl, Hsx.extractDataConNs decl, Hsx.extractFieldNs decl]
    used_types = Set.map canonicalize' $ Hsx.extractTypeConNs decl
    impl_types = catMaybes $ Set.toList $ Set.map (Ident_Env.getDepDataType globalEnv (Ident_Env.fromHsk modul)) used_names
  in
    [ ((pos, decl), name, Set.toList (Set.union used_names used_types) ++ impl_types) | name <- names ]

{-|
  ???
-}
handleDuplicateEdges :: [(HskDecl, Ident_Env.Name, [Ident_Env.Name])] -> [(HskDecl, HskDeclDepGraphKey, [HskDeclDepGraphKey])]
handleDuplicateEdges edges
    = edges
    & groupByFull (\(_,x,_) -> x)
    & concatMap handleGroup
    & List.sortBy (let f ((n, _), _, _) = n in \a1 a2 -> compare (f a1) (f a2))
    & mapAccumLsnd (\ mapIdent decl@((n,d), (bk, k), (nl,l)) ->
                     ( if isClass decl || isInstance decl then Map.insert k n mapIdent else mapIdent
                     , ((n,d), (bk, k), maybe id (\i l -> let v = (Just i, k) in if v `elem` l then l else v : l) nl (map (\k -> (Map.lookup k mapIdent, k)) l))))
                   Map.empty
    where handleGroup edges
              = edges
              & partition_single isTypeAnnotation
              & (\ee -> case ee of
                  (Nothing, edges) -> edges
                  (Just (_, _, l0), edges) -> map (\(d, n, l1) -> (d, n, l0 ++ l1)) edges)
              & (\edges -> if ambiguous_edges edges then error (Msg.ambiguous_decl_definitions edges) else edges)
              & partition_single isClass
              & (\(edge_c, edges) ->
                  let pos_c = fmap (\((n, _), _, _) -> n) edge_c in
                  mapAccumLsnd (\n ((decl_n, decl_d), decl_k, decl_l) -> (Just decl_n, ((decl_n, decl_d), (case n of Nothing -> Nothing ; _ -> Just decl_n, decl_k), (n, decl_l))))
                               pos_c
                               edges
                  & maybe id (\(d, k, l) -> (:) (d, (pos_c, k), (Nothing, l))) edge_c)

          ambiguous_edges edges
              = length edges > 1 && any (\e -> not (isClass e || isInstance e)) edges
          mapAccumLsnd f acc = snd . mapAccumL f acc
          partition_single f l = case List.partition f l of ([], l) -> (Nothing, l)
                                                            ([x], l) -> (Just x, l)
                                                            _ -> error Msg.unsupported_semantics_decl
          groupByFull f = Map.elems . foldr (\x map -> let k = f x in Map.insert k (x : maybe [] id (Map.lookup k map)) map) Map.empty
          isTypeAnnotation ((_, Hsx.TypeSig _ _ _), _ , _) = True
          isTypeAnnotation _ = False
          isInstance ((_, Hsx.InstDecl _ _ _ _), _, _) = True
          isInstance _ = False
          isClass ((_, Hsx.ClassDecl _ _ _ _ _), _, _) = True
          isClass _ = False



-- In Haskell definitions may appear anywhere in a source file, but in
-- Isar/HOL (like in ML), definitions that are used in another definition
-- must appear lexically before that other definition.

{-|
  This function takes a dependency graph of Haskell declarations and linearises it, such that
  functions are declared before they are used by another function definition. The result is a
  list of list of declaration each list of declarations forms a set of declarations that depend
  on each other in a mutually recursive way.
-}

flattenDeclDepGraph :: HskDeclDepGraph -> [[Hsx.Decl ()]]
flattenDeclDepGraph (HskDeclDepGraph (graph, fromVertex, _))
    -- We first partition the graph into groups of mutually-dependent declarations
    -- (i.e. its strongly-connected components); we then sort these components according
    -- their dependencies (decls used later must come first.)
    -- 
    -- Additionally we sort each declaration in such a component source-line wise, 
    -- and also sort source-line wise if two components are completely independent.
    -- Objective: To preserve the ordering of the original source code file as
    --            much as possible.
    = let declFromVertex v = (let ((_, decl),_,_) = fromVertex v in decl)
      in map (map declFromVertex)
             $ List.sortBy orderComponents_ByDependencies
                 (map (List.sortBy orderVertices_BySourceLine . Tree.flatten) $ scc graph)
    where
      orderVertices_BySourceLine v1 v2
          = let (decl1,_,_) = fromVertex v1
                (decl2,_,_) = fromVertex v2
            in Hsx.orderDeclsBySourceLine decl1 decl2

      orderComponents_ByDependencies vs1 vs2
          = let used_vs_in_1 = concatMap (reachable graph) vs1
                used_vs_in_2 = concatMap (reachable graph) vs2
            in if (isContained used_vs_in_1 vs2)      -- does vs2 define stuff needed in vs1?
               then assert (not (isContained used_vs_in_2 vs1)) $ GT
               else if (isContained used_vs_in_2 vs1) -- does vs1 define stuff needed in vs2?
                    then assert (not (isContained used_vs_in_1 vs2)) $ LT
                    else                              -- vs1 and vs2 are independant.
                        let (decl1,_,_) = fromVertex (head vs1)
                            (decl2,_,_) = fromVertex (head vs2)
                        in Hsx.orderDeclsBySourceLine decl1 decl2
            where 
              isContained xs ys = not (null (List.intersect xs ys))

arrangeDecls :: Bool -> Ident_Env.GlobalE -> Hsx.ModuleName () -> [Hsx.Decl ()] -> [[Hsx.Decl ()]]
arrangeDecls ignoreNotInScope globalEnv modul = flattenDeclDepGraph . makeDeclDepGraph ignoreNotInScope globalEnv modul

