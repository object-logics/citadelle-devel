{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Author: Tobias C. Rittweiler, TU Muenchen
-}

module Importer.Gensym where

import Control.Monad.State

import qualified Language.Haskell.Exts as Hsx (Name(..), QName(..))
import qualified Importer.Isa as Isa (Name(..))

data Count = Count { sym :: Int, pos :: Int }

posInit = 0
countInit = Count {sym = 0, pos = posInit}

newtype GensymM a = GensymM (State Count a)
  deriving (Monad, Functor, Applicative, MonadFix, MonadState Count)

gensym :: String -> GensymM String
gensym prefix = do count <- get
                   put (count { sym = sym count + 1 })
                   return (prefix ++ show (sym count))

setPos :: Int -> GensymM ()
setPos pos = do count <- get
                put (count { pos = pos })

askPos :: GensymM Int
askPos = do count <- get
            return $ pos count

genHsName :: Hsx.Name l -> GensymM (Hsx.Name l)
genHsName (Hsx.Ident  l prefix) = liftM (Hsx.Ident l)  (gensym prefix) 
genHsName (Hsx.Symbol l prefix) = liftM (Hsx.Symbol l) (gensym prefix) 

genHsQName :: Hsx.QName l -> GensymM (Hsx.QName l)
genHsQName (Hsx.Qual l m prefix)  = liftM (Hsx.Qual l m) (genHsName prefix)
genHsQName (Hsx.UnQual l prefix)  = liftM (Hsx.UnQual l) (genHsName prefix)

genIsaName :: Isa.Name -> GensymM Isa.Name
genIsaName (Isa.QName t prefix) = liftM (Isa.QName t) (gensym prefix)
genIsaName (Isa.Name prefix)    = liftM Isa.Name      (gensym prefix)

evalGensym :: Count -> GensymM a -> a
evalGensym init (GensymM state) = evalState state init

runGensym :: Count -> GensymM a -> (a, Count)
runGensym init (GensymM state)  = runState state init
