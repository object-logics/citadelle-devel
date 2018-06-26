{-| Author: Tobias C. Rittweiler, TU Muenchen

Internal importer main interfaces.
-}

module Importer.Conversion (importFiles, importProject) where

import Importer.Library

import qualified Data.Generics as G
import qualified Data.List as List
import qualified Language.Haskell.Interpreter as I
import Text.PrettyPrint (render)

import System.FilePath
import System.Directory
import System.IO

import Importer.Adapt (Adaption (..), AdaptionTable, readAdapt, preludeFile)
import Importer.Configuration
import Importer.Convert
import Importer.Printer (pprint)

import qualified Importer.Ident_Env as Ident_Env (GlobalE)
import qualified Importer.Isa as Isa (Module (..), Stmt (..), ThyName (..))
import qualified Importer.Hsx as Hsx
import qualified Importer.Conversion.SML as SML


importProject :: Config -> FilePath -> Bool -> Maybe ([String], [String], String, String) -> [String] -> IO ()
importProject config adaptDir metaParseShallow metaParse hskContents = do
  adapt <- readAdapt adaptDir
  runConversion config (convertFiles adapt metaParseShallow metaParse hskContents)

importFiles :: [FilePath] -> Maybe FilePath -> Bool -> Bool -> Bool -> Maybe FilePath -> Bool -> Bool -> FilePath -> Bool -> Maybe ([String], [String], String, String) -> [String] -> IO ()
importFiles files out exportCode tryImport onlyTypes basePathAbs getIgnoreNotInScope absMutParams
  = importProject (defaultConfig defaultCustomisations files out exportCode tryImport onlyTypes basePathAbs getIgnoreNotInScope absMutParams)

convertFiles :: Adaption -> Bool -> Maybe ([String], [String], String, String) -> [String] -> Conversion ()
convertFiles adapt metaParseShallow metaParse hskContents = do

  inFiles <- getInputFilesRecursively
  outDir <- getOutputDir
  exportCode <- getExportCode
  tryImport <- getTryImport
  onlyTypes <- getOnlyTypes
  basePathAbs <- getBasePathAbs
  ignoreNotInScope <- getIgnoreNotInScope
  absMutParams <- getAbsMutParams
  custs <- getCustomisations
  
  exists <- liftIO $ mapM doesDirectoryExist outDir
  when (case exists of Just False -> True ; _ -> False) $ liftIO $ maybe (return ()) createDirectory outDir
  hskContents' <- liftIO $ mapM (case metaParse of Nothing -> return . (\code -> (code, []))
                                                   Just (load, imports, code, hskName) -> \hsk_ct -> do
                                                     let s = I.parens code ++ " " ++ show hsk_ct
                                                     res <- I.runInterpreter $ do
                                                              mapM (\basePathAbs -> I.set [I.searchPath I.:= [basePathAbs]]) basePathAbs
                                                              I.loadModules load
                                                              I.setImports ("Prelude" : imports)
                                                              I.interpret s (I.as :: IO (String, [(Int, Int, (String, [(String, String)]))])) >>= liftIO
                                                     return $ case res of Right (code, report) -> (hskName ++ " = " ++ code, report) ; Left l -> error (show l))
                                hskContents
  let (hskContents'0, report) = unzip hskContents'
  units <- parseHskFiles tryImport onlyTypes basePathAbs (map Right hskContents'0 ++ map Left (filter Hsx.isHaskellSourceFile inFiles))
  let (adaptTable : _, convertedUnits) = map_split (convertHskUnit custs exportCode ignoreNotInScope absMutParams adapt) units

  liftIO $ maybe (return ()) (\outDir -> copyFile (preludeFile adapt) (combine outDir (takeFileName (preludeFile adapt)))) outDir
  sequence_ (map (writeIsaUnit adaptTable (reservedKeywords adapt)) convertedUnits)
  liftIO $ case outDir of Nothing -> putStrLn $ SML.gshow ( List.nubBy (let f (Isa.Module t _ _ _) = t in \m1 m2 -> f m1 == f m2)
                                                             $ concatMap (\(IsaUnit l _ _) -> (if metaParseShallow then G.everywhere (G.mkT (\s -> case s of Isa.Function f -> Isa.ML f; x -> x)) else id) l) convertedUnits
                                                          , report)
                          _       -> return ()


writeIsaUnit :: AdaptionTable -> [String] -> IsaUnit -> Conversion ()
writeIsaUnit adapt reserved (IsaUnit thys custThys env)
    = mapM_ writeCustomTheory custThys >>
      mapM_ (writeTheory adapt reserved env) thys

writeCustomTheory :: CustomTheory -> Conversion ()
writeCustomTheory cust = 
    do let src = getCustomTheoryPath cust
           filename = takeFileName src
       getOutputDirMaybe (\outDir -> liftIO $ copyFile src (combine outDir filename))

writeTheory :: AdaptionTable -> [String] -> Ident_Env.GlobalE -> Isa.Module -> Conversion ()
writeTheory adapt reserved env thy @ (Isa.Module (Isa.ThyName thyname) _ _ _) = do
  let content = render (pprint adapt reserved env thy)
  let dstName = content `seq` map (\c -> if c == '.' then '_' else c) thyname ++ ".thy"
  getOutputDirMaybe (\outLoc -> do
    let dstPath = combine outLoc dstName
    liftIO $ hPutStrLn stderr $ "writing " ++ dstName ++ "..."
    liftIO $ writeFile dstPath content)

getOutputDirMaybe f = getOutputDir >>= maybe (return ()) f
