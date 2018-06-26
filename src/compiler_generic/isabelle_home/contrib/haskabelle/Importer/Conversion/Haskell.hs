module Importer.Conversion.Haskell where

import qualified Data.Data as D
import qualified Data.Generics as G

type SS' = String
type SS = SS' -> SS'

gshows :: D.Data a => a -> SS
gshows = render `G.extQ` (shows :: String -> SS) where
  render t
    | isTuple = commaSlots' '(' "," ')'
    | isListEmpty = showString "[]"
    | isList = commaSlots '(' ":" ')'
    | isSingleConst = constructor

    | otherwise = showChar '('
                . constructor
                . build " "
                . showChar ')'

    where constructor = showString . D.showConstr . D.toConstr $ t

          build s = foldr (.) id . D.gmapQ ((showString s .) . gshows) $ t
          commaSlots c1 s c2 = showChar c1 . drop (length s) . build s . showChar c2
          commaSlots' c1 s c2 = -- this particular arrangement of tuples is following the ordering chosen in Haskabelle
            case D.gmapQ gshows t of x : xs -> foldl (\x1 x2 -> showChar c1 . x1 . showString s . x2 . showChar c2) x xs
          filt s = filter (not . flip elem s) (constructor "")

          isTuple = all (==',') (filt "()")
          isListEmpty = null (filt "[]")
          isList = constructor "" == "(:)"
          isSingleConst = null (D.gmapQ (\_ -> ()) t)
