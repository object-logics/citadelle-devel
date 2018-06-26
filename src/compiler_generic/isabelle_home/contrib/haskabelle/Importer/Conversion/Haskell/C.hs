{-# LANGUAGE DeriveDataTypeable #-}

module Importer.Conversion.Haskell.C where

import Control.Monad
import Data.Function
import System.Directory
import System.FilePath
import System.IO
import Text.Parsec.String (Parser)
import Text.Parsec

import qualified Data.ByteString as B
import qualified Data.Data as D
import qualified Data.Generics as G
import qualified Language.C as C
import qualified Language.C.Comments as CC
import qualified Language.C.Data.Position as P
import qualified Language.C.System.GCC as GCC
import qualified Language.C.System.Preprocess as CP
import qualified Importer.Conversion.Markup as Markup

parseComments fic = do
  f <- readFile fic
  lines f
    & foldl (\(buf_all, buf_local) line ->
               case parse directive "" line of Left _ -> (buf_all, line : buf_local)
                                               Right (l, s) -> (Left (s, read l :: Int) : flush_local buf_all buf_local, []))
            ([], [])
    & (\(buf_all, buf_local) -> reverse $ flush_local buf_all buf_local)
    & foldl (\((fic, row), l_comm) line -> 
               case line of
                 Left fic_row -> (fic_row, l_comm)
                 Right body ->
                   ((fic, row),
                    map (\x -> x { CC.commentPosition = let pos = CC.commentPosition x in
                                                        P.position (P.posOffset pos) fic (row + P.posRow pos - 1) (P.posColumn pos) })
                        (CC.commentsFromString $ unlines body) : l_comm))
            (("", 1), [])
    & (\ (_, l_comm) -> concat $ reverse l_comm)
    & return
 where
  flush_local buf_all [] = buf_all
  flush_local buf_all buf_local = Right (reverse buf_local) : buf_all

  directive = do
    char '#'
    whitespace
    i <- many1 digit
    whitespace
    char '"'
    s <- manyTill anyChar (try $ char '"')
    manyTill (digit <|> char ' ') eof
    return (i, s)

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \t"

parseCFilePre0 :: Maybe FilePath -> FilePath -> Either C.ParseError a -> IO (a, ([Comment], [Int]))
parseCFilePre0 fic_orig fic_pre =
  either (error . show) (\x -> do cc <- parseComments (case fic_orig of {Nothing -> fic_pre; Just fic_orig -> fic_orig})
                                  l <-
                                    case fic_orig of Nothing -> return []
                                                     Just fic_orig -> do s <- readFile fic_orig
                                                                         return $ map length $ lines s
                                  return (x, (map map_comment cc, l)))

parseCFilePre :: Maybe FilePath -> FilePath -> IO (C.CTranslUnit, ([Comment], [Int]))
parseCFilePre fic_orig fic_pre =
  C.parseCFilePre fic_pre >>= parseCFilePre0 fic_orig fic_pre

parseCFile' :: CP.Preprocessor cpp => cpp -> [String] -> FilePath -> IO (Maybe FilePath, Either C.ParseError C.CTranslUnit)
parseCFile' cpp args input_file = do
    (out, input_stream) <- if not (CP.isPreprocessed input_file)
                           then do outputFile <- mkOutputFile Nothing getOutputFileName input_file
                                   let cpp_args = (CP.rawCppArgs args input_file) { CP.outputFile = Just outputFile }
                                   ic <- CP.runPreprocessor cpp cpp_args >>= handleCppError
                                   return $ (Just outputFile, ic)
                           else do ic <- C.readInputStream input_file
                                   return $ (Nothing, ic)
    return$ (out, C.parseC input_stream (P.initPos input_file))
    where
    handleCppError (Left exitCode) = fail $ "Preprocessor failed with " ++ show exitCode
    handleCppError (Right ok)      = return ok

parseC' :: C.InputStream -> IO ((C.CTranslUnit, ([Comment], [Int])), [(Int, Int, (String, [(String, String)]))])
parseC' input = do
  fic_orig <- mkOutputFile Nothing id "input.c"
  B.writeFile fic_orig input
  (fic_pre, parsed) <- parseCFile' (GCC.newGCC "cpp") [] fic_orig
  parsed' <- parseCFilePre0 (Just fic_orig) (maybe fic_orig id fic_pre) parsed
  mapM removeFile fic_pre
  removeFile fic_orig
  return $ ( G.everywhere (G.mkT (\pos -> if P.isSourcePos pos then P.position (P.posOffset pos) "" (P.posRow pos) (P.posColumn pos) else pos)) parsed'
           , case parsed' of (_, (l_comm, _)) -> map (\(Comment { commentPosition = pos, commentText = txt }) -> (P.posOffset pos, P.posOffset pos + length txt, (Markup.to_ML Markup.ML_COMMENT, []))) l_comm)

--------------------------------------------------------------------------------
-- Same types as language-c-comments with the addition of Data as derived entity

data CommentFormat = SingleLine | MultiLine deriving (Eq,Show,D.Data)

data Comment = Comment {
  -- | The position of the comment within the source file.
  commentPosition :: C.Position,
  -- | The text of a comment (including the comment marks).
  commentText :: String,
  -- | The format of a comment (single- or multi-line).
  commentFormat :: CommentFormat
} deriving (Eq,Show,D.Data)

map_commentFormat x = case x of
  CC.SingleLine -> SingleLine
  CC.MultiLine -> MultiLine

map_comment x =
  Comment { commentPosition = CC.commentPosition x
          , commentText = CC.commentText x
          , commentFormat = map_commentFormat $ CC.commentFormat x }



-----------------------------------------------------------------------------
-- |
-- Module      :  Language.C.System.Preprocess
-- Copyright   :  (c) 2008 Benedikt Huber
-- License     :  BSD-style
-- Maintainer  :  benedikt.huber@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Invoking external preprocessors.
-----------------------------------------------------------------------------

-- | file extension of a preprocessed file
preprocessedExt :: String
preprocessedExt = ".i"

-- | create an output file, given  @Maybe tmpdir@ and @inputfile@
mkOutputFile :: Maybe FilePath -> (FilePath -> FilePath) -> FilePath -> IO FilePath
mkOutputFile tmp_dir_opt getOutputFileName input_file =
    do tmpDir <- getTempDir tmp_dir_opt
       mkTmpFile tmpDir (getOutputFileName input_file)
    where
    getTempDir (Just tmpdir) = return tmpdir
    getTempDir Nothing       = getTemporaryDirectory

-- | compute output file name from input file name
getOutputFileName :: FilePath -> FilePath
getOutputFileName fp | hasExtension fp = replaceExtension filename preprocessedExt
                     | otherwise       = addExtension filename preprocessedExt
    where
    filename = takeFileName fp

-- | create a temporary file
mkTmpFile :: FilePath -> FilePath -> IO FilePath
mkTmpFile tmp_dir file_templ = do
    -- putStrLn $ "TmpDir: "++tmp_dir
    -- putStrLn $ "FileTempl: "++file_templ
    (path,file_handle) <- openTempFile tmp_dir file_templ
    hClose file_handle
    return path
