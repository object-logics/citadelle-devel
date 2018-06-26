{-# OPTIONS_GHC -O -o bin/haskabelle_bin -odir build -hidir build -stubdir build #-}

{-  Author: Florian Haftmann, TU Muenchen

Toplevel interface to Haskabelle importer.
-}

module Main where

import Data.Function
import qualified Data.List as List

import System.Environment (getArgs, getProgName)
import System.Exit (exitWith, ExitCode (ExitFailure))
import System.IO

import Importer.Conversion (importProject, importFiles)
import Importer.Adapt (readAdapt, Adaption (..))
import Importer.Configuration (readConfig)
import Importer.Version (version)

{-
  Usage of the haskabelle binary:

  haskabelle_bin --internal <ADAPT> <SRC1> .. <SRCn> <DST>
  haskabelle_bin --internal <ADAPT> --config <CONFIG>
  haskabelle_bin --version

  Import Haskell files <SRC1> .. <SRCn> into Isabelle theories in directory
  <DST>, optionally using customary adaption in directory <ADAPT> OR import
  Haskell files according to configuration file <CONFIG>.
-}

readBool :: String -> IO Bool
readBool "true" = return True
readBool "false" = return False
readBool _ = exitWith (ExitFailure 2)

tryImport = False
onlyTypes = False
basePathAbs = Nothing
ignoreNotInScope = False
absMutParams = False
metaParseShallow = False
metaParse = Nothing
hskContents = []

mainInterface :: [(String, [String])] -> IO ()
mainInterface (("internal", [adaptDir]) : ("export", [exportVar]) : ("config", [configFile]) : []) = do
  exportCode <- readBool exportVar
  config <- readConfig configFile exportCode
  importProject config adaptDir metaParseShallow metaParse hskContents
mainInterface (("internal", [adaptDir]) : ("export", [exportVar]) : ("try-import", [tryImportVar]) : ("only-types", [onlyTypesVar]) : ("base-path-abs", basePathAbs) : ("ignore-not-in-scope", [ignoreNotInScopeVar]) : ("abstract-mutual-data-params", [absMutParamsVar]) : ("dump-output", []) : ("meta-parse-shallow", [metaParseShallowVar]) : ("meta-parse-load", metaParseLoad) : ("meta-parse-imports", metaParseImports) : ("meta-parse-code", metaParseCode) : ("hsk-name", hskName) : ("hsk-contents", hskContents) : ("files", srcs) : []) = do
  tryImport <- readBool tryImportVar
  onlyTypes <- readBool onlyTypesVar
  ignoreNotInScope <- readBool ignoreNotInScopeVar
  absMutParams <- readBool absMutParamsVar
  metaParseShallow <- readBool metaParseShallowVar
  mainInterfaceDump exportVar srcs tryImport onlyTypes (case basePathAbs of [] -> Nothing ; [x] -> Just (x)) ignoreNotInScope absMutParams adaptDir metaParseShallow (case (metaParseLoad, metaParseImports, metaParseCode, hskName) of ([], [], [], []) -> Nothing ; (l, i, [c], [n]) -> Just (l, i, c, n)) hskContents
mainInterface (("internal", [adaptDir]) : ("export", [exportVar]) : ("files", srcs @ [_]) : []) = mainInterfaceDump exportVar srcs tryImport onlyTypes basePathAbs ignoreNotInScope absMutParams adaptDir metaParseShallow metaParse hskContents
mainInterface (("internal", [adaptDir]) : ("export", [exportVar]) : ("files", srcs_dst @ (_ : _ : _)) : []) = do
  exportCode <- readBool exportVar
  importFiles (init srcs_dst) (Just (last srcs_dst)) exportCode tryImport onlyTypes basePathAbs ignoreNotInScope absMutParams adaptDir metaParseShallow metaParse hskContents

mainInterface (("internal", arg) : args) = do
  hPutStrLn stderr "Error calling internal haskabelle binary. Wrong parameters:"
  hPutStrLn stderr ("  " ++ show arg ++ " " ++ show args)
  exitWith (ExitFailure 2)

mainInterface (("version", _) : _) = do
  putStrLn (version ++ ".")

mainInterface _ = do
  hPutStrLn stderr "Do not invoke linked Haskabelle binary directly"
  hPutStrLn stderr "  -- invoke it as described in the Haskabelle manual."
  hPutStrLn stderr ""
  hPutStrLn stderr "Have a nice day!"
  hPutStrLn stderr ""
  exitWith (ExitFailure 2)

mainInterfaceDump exportVar srcs tryImport onlyTypes basePathAbs ignoreNotInScope absMutParams adaptDir metaParseShallow metaParse hskContents = do
  exportCode <- readBool exportVar
  importFiles srcs Nothing exportCode tryImport onlyTypes basePathAbs ignoreNotInScope absMutParams adaptDir metaParseShallow metaParse hskContents

main :: IO ()
main = getArgs >>= mapM (return . \s -> case s of '-' : '-' : s -> Left s ; s -> Right s)
               >>= (\l ->
                       let isLeft = either (\_ -> True) (\_ -> False)
                           isRight = either (\_ -> False) (\_ -> True)
                       in l
                        & List.groupBy (\a1 a2 -> isRight a1 && isRight a2)
                        & map (\t -> case t of [Left t] -> Left t ; l -> Right (map (\(Right e) -> e) l))
                        & List.groupBy (\a1 a2 -> isLeft a1 && isRight a2)
                        & map (\l -> case l of [Left t] -> (t, [])
                                               [Left t0, Right t1] -> (t0, t1))
                        & return)
               >>= mainInterface
