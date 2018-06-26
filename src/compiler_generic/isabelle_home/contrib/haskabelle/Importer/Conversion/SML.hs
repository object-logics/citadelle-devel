module Importer.Conversion.SML where

import qualified Data.Char as Char
import qualified Data.Data as D
import qualified Data.Generics.Aliases as G
import qualified Text.Printf as Printf

render_string_wrap = True

char_escape c =    c >= '\b' && c <= '\n'
                || c == '\r'
                || c == '"'

char c =    char_escape c
         || c >= ' ' && c <= '~' && (c /= '\\' && c /= '<' {- the escaping of string comments for future ML parsing to succeed -})

type SS' = String
type SS = SS' -> SS'

monad_String = showString
monad_Char = showChar
monad_Drop = drop

gshows :: D.Data a => a -> SS
gshows = render `G.extQ` (render_bool :: Bool -> SS)
                `G.extQ` (render_string :: String -> SS)
                `G.extQ` (render_char :: Char -> SS)
                `G.extQ` (render_int :: Int -> SS)
                `G.extQ` (render_integer :: Integer -> SS) where
  render_bool b = monad_String $ if b then "true" else "false"
  render_string =
    let (monad_String_show, monad_String') = if render_string_wrap then (monad_String' . show, \s -> monad_String ("From.string " ++ s)) else (shows, monad_String) in
    \s -> if all char s then monad_String_show s
          else monad_String' $ "\"" ++ concatMap (\c -> if char c && not (char_escape c) then [c]
                                                        else Printf.printf "\\%03d" (Char.ord c)) s ++ "\""
  render_char c = monad_Char '#' . render_string [c]
  render_int i = monad_String "From.nat " . if i < 0 then monad_Char '~' . shows (-i) else shows i
  render_integer = render_int
  render t
    | isTuple = commaSlots' '(' "," ')'
    | isListEmpty = monad_String "[]"
    | isList = commaSlots '(' "::" ')'
    | isOption = case D.showConstr . D.toConstr $ t of
                   "Just" -> monad_String "SOME" . commaSlots '(' "," ')'
                   "Nothing" -> monad_String "NONE"
    | isSingleConst = constructor

    | otherwise = constructor
                . commaSlots '(' "," ')'

    where constructor = monad_String . D.showConstr . D.toConstr $ t

          build s = foldr (.) id . D.gmapQ ((monad_String s .) . gshows) $ t
          commaSlots c1 s c2 = monad_Char c1 . monad_Drop (length s) . build s . monad_Char c2
          commaSlots' c1 s c2 = -- this particular arrangement of tuples is following the ordering chosen in Haskabelle
            case D.gmapQ gshows t of x : xs -> foldl (\x1 x2 -> monad_Char c1 . x1 . monad_String s . x2 . monad_Char c2) x xs
          filt s = filter (not . flip elem s) (constructor "")

          isTuple = all (==',') (filt "()")
          isListEmpty = null (filt "[]")
          isList = constructor "" == "(:)"
          isOption = let c = constructor "" in c == "Just" || c == "Nothing"
          isSingleConst = null (D.gmapQ (\_ -> ()) t)

gshow f = gshows f ""
