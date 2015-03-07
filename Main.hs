{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NullaryTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}

import System.Environment
import Control.Concurrent(forkIO, newEmptyMVar, takeMVar, putMVar)
import Control.Exception(Exception, throwIO)
import Control.Monad(void, unless)
import Control.Applicative((<$>))

import System.Directory(getHomeDirectory)
import System.IO(hGetContents)
import System.IO.Temp(withSystemTempDirectory)
import System.Exit(ExitCode(..))
import System.FilePath
import qualified System.Process as P

import Data.Monoid
import Data.Typeable(Typeable)
import Data.Version(parseVersion, Version)
import Data.List(intercalate, intersperse, isPrefixOf, isInfixOf, nub)
import Data.List.Split(splitOn)
import Data.Reflection
import qualified Data.ByteString.Lazy as L
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy.Encoding as TL

import qualified Codec.Compression.GZip as GZ
import qualified Codec.Archive.Tar as Tar

import Text.ParserCombinators.ReadP(readP_to_S)

import qualified Distribution.Text as C
import qualified Distribution.Compiler as C
import qualified Distribution.System as C
import qualified Distribution.Version as C
import Distribution.Package(PackageName(..), PackageId, PackageIdentifier(..))
import qualified Distribution.Package as C
import qualified Distribution.ParseUtils as C
import qualified Distribution.PackageDescription as C
import qualified Distribution.PackageDescription.Parse as C
import qualified Distribution.PackageDescription.Configuration as C

import Unsafe.Coerce

data Reason
    = CreateSandboxFailed
    | ResolveDepFailed
    | GlobalPackagesFailed
    deriving(Show, Typeable)

data ProcessException
    = ProcessException Reason ExitCode String
    deriving(Show, Typeable)

instance Exception ProcessException

data ParseLineException
    = ParseLineException String
    deriving(Show, Typeable)

instance Exception ParseLineException

newtype TempDirectory = TempDirectory
    { getTempDirectory :: FilePath
    }

withTempDirectory :: (Given TempDirectory => IO a) -> IO a
withTempDirectory m = withSystemTempDirectory "cabal-dep-graph.XXXXX" $ \f ->
    give (TempDirectory f) m

newtype CabalInstall = CabalInstall
    { cabalInstallPath :: FilePath
    }

class Sandbox

withSandbox :: (Given TempDirectory, Given CabalInstall) => (Sandbox => IO a) -> IO a
withSandbox m = do
    (_, Just o, Just e, ph) <- P.createProcess
        (P.proc (cabalInstallPath given) ["sandbox", "init"])
        { P.cwd     = Just (getTempDirectory given)
        , P.std_out = P.CreatePipe
        , P.std_err = P.CreatePipe
        }
    es <- newEmptyMVar
    _ <- forkIO $ void $ hGetContents o
    _ <- forkIO $ hGetContents e >>= putMVar es
    x <- P.waitForProcess ph
    unless (x == ExitSuccess) $
        takeMVar es >>= throwIO . ProcessException CreateSandboxFailed x
    run m ()
  where
    run :: (Sandbox => IO a) -> (() -> IO a)
    run = unsafeCoerce

resolveDeps :: (Given TempDirectory, Given CabalInstall) => [String] -> IO [(PackageId, Version)]
resolveDeps pkgs = do
    (_, Just o, Just e, ph) <- P.createProcess
        (P.proc (cabalInstallPath given) $ "install":"--dry-run":pkgs)
        { P.cwd     = Just (getTempDirectory given)
        , P.std_out = P.CreatePipe
        , P.std_err = P.CreatePipe
        }

    os <- newEmptyMVar
    es <- newEmptyMVar

    _ <- forkIO $ hGetContents o >>= putMVar os
    _ <- forkIO $ hGetContents e >>= putMVar es
    x <- P.waitForProcess ph
    unless (x == ExitSuccess) $
        takeMVar es >>= throwIO . ProcessException ResolveDepFailed x
    
    mapM (\l -> maybe (throwIO $ ParseLineException l) return $ readDepLine l) . drop 2 . lines =<< takeMVar os

globalPackages :: (Given TempDirectory, Given CabalInstall, Sandbox) => IO [PackageId]
globalPackages = do
    (_, Just o, Just e, ph) <- P.createProcess
        (P.proc (cabalInstallPath given) ["sandbox", "hc-pkg", "list"])
        { P.cwd     = Just (getTempDirectory given)
        , P.std_out = P.CreatePipe
        , P.std_err = P.CreatePipe
        }

    os <- newEmptyMVar
    es <- newEmptyMVar

    _ <- forkIO $ hGetContents o >>= putMVar os
    _ <- forkIO $ hGetContents e >>= putMVar es
    x <- P.waitForProcess ph
    unless (x == ExitSuccess) $
        takeMVar es >>= throwIO . ProcessException GlobalPackagesFailed x

    mapM (\p -> maybe (throwIO $ ParseLineException p) return . readPkgVersion $ dropWhile (== ' ') p)
        . filter (not . ("(" `isInfixOf`))
        . filter (" " `isPrefixOf`)
        . lines =<< takeMVar os

readVersion :: String -> Maybe Version
readVersion v = case readP_to_S parseVersion v of
    [] -> Nothing
    l  -> Just . fst $ last l

readPkgVersion :: String -> Maybe PackageId
readPkgVersion pv = do
    let i = splitOn "-" pv
        p = intercalate "-" $ init i
    v <- readVersion (last i)
    Just $ PackageIdentifier (PackageName p) v

readDepLine :: String -> Maybe (PackageId, Version)
readDepLine s = case break (== ' ') s of
    (pv, "") -> (\p -> (p, C.packageVersion p)) <$> readPkgVersion pv
    (pv, o) | "latest:" `isInfixOf` o -> do
        lv <- readVersion . dropWhile (== ' ') . tail $ dropWhile (/= ':') o
        (,lv) <$> readPkgVersion pv
    _ -> Nothing

newtype IndexFile = IndexFile { getIndexFile :: FilePath }

getIndices :: Given IndexFile => IO [(PackageId, L.ByteString)]
getIndices = L.readFile (getIndexFile given) >>= loop . Tar.read . GZ.decompress
  where
    loop :: Tar.Entries Tar.FormatError -> IO [(PackageId, L.ByteString)]
    loop (Tar.Next e es) = do
        let mbnxt = do
                let p:vs:_ = splitDirectories (Tar.entryPath e)
                v <- readVersion vs
                case Tar.entryContent e of
                        Tar.NormalFile c _ -> Just (C.PackageIdentifier (C.PackageName p) v, c)
                        _ -> Nothing
        maybe id (:) mbnxt <$> loop es
    loop Tar.Done      = return []
    loop (Tar.Fail e)  = throwIO e

data CabalConfigureException
    = CabalParseException PackageId C.PError
    | FinalizeException PackageId [C.Dependency]
    deriving(Show, Typeable)
instance Exception CabalConfigureException

checkDep :: C.Dependency -> PackageId -> Bool
checkDep (C.Dependency n r) (C.PackageIdentifier n' v)
    | n == n'   = C.withinRange v r
    | otherwise = False

data CabalConfig = CabalConfig
    { flagAssignment :: C.FlagAssignment
    , platform       :: C.Platform
    , compilerId     :: C.CompilerId
    }

cabalToDeps :: Given CabalConfig => [C.PackageId] -> PackageId -> String -> IO [C.Dependency]
cabalToDeps pkgs pkg s = case C.parsePackageDescription s of
    C.ParseFailed e -> throwIO $ CabalParseException pkg e
    C.ParseOk _ gpd ->
        return (C.finalizePackageDescription (flagAssignment given) (\d -> any (checkDep d) pkgs) (platform given) (compilerId given) [] gpd)
        >>= either (throwIO . FinalizeException pkg) return
        >>= return . C.buildDepends . fst
    
data DepGraph = DepGraph
    { packages     :: [((PackageId, Version), Bool)]
    , globals      :: [PackageId]
    , dependencies :: [(PackageId, [C.Dependency])]
    } deriving Show


createDepGraph :: (Given TempDirectory, Given CabalInstall, Sandbox, Given IndexFile, Given CabalConfig) => [String] -> IO DepGraph
createDepGraph ps = do
    toInstall <- resolveDeps ps
    indices   <- getIndices
    globals'  <- globalPackages
    deps      <- return (filter (\(p,_) -> p `elem` map fst toInstall) indices)
        >>= mapM (\(p,d) -> fmap (p,) $ cabalToDeps (globals' ++ map fst toInstall) p . TL.unpack $ TL.decodeUtf8 d)
    let uniqueDeps  = nub $ concatMap (map (\(C.Dependency n _) -> n) . snd) deps
        needGlobals = filter (\pid -> C.packageName pid `elem` uniqueDeps) globals'
    return $ DepGraph
        { packages     = map (\p -> (p, C.packageName (fst p) `elem` map PackageName ps)) toInstall
        , globals      = needGlobals
        , dependencies = deps
        }

data DotConfig = DotConfig
    { dotName :: T.Text
    }

renderDot :: Given DotConfig => DepGraph -> B.Builder
renderDot DepGraph{..} =
    "digraph " <> B.fromText (dotName given) <> " {\n" <>
    mconcat (map renderPackage packages) <> "\n" <>
    mconcat (map renderGlobal globals) <> "\n" <>
    mconcat (map renderEdges dependencies) <>
    "}"
  where
    fromDisp = B.fromString . C.display
    renderAttrs as =
        "[" <> mconcat (intersperse "; " $ map (\(k,v) -> k <> " = " <> v) as) <> "];\n"

    doubleQuote s = B.singleton '"' <> s <> B.singleton '"'
    renderPackage ((p,v),s) =
        let label = doubleQuote $ fromDisp p
            ood   = C.packageVersion p /= v
        in "  " <> (doubleQuote . fromDisp . C.packageName) p <> renderAttrs
            ((if s then (("color", "red"):) else id) $ [("fillcolor", if ood then "yellow" else "white"), ("style", "filled"), ("shape", "box"), ("label", label)])

    renderGlobal p = "  " <> (doubleQuote . fromDisp . C.packageName) p <> renderAttrs
        [("fillcolor", "gray"), ("style", "filled"), ("shape", "box"), ("label", doubleQuote $ fromDisp p)]

    renderEdges (p, ds) = (mconcat . map (renderEdge p)) ds <> "\n"
    renderEdge p (C.Dependency d v) =
        "  " <>
        (doubleQuote . fromDisp . C.packageName) p <>
        " -> " <>
        (doubleQuote . fromDisp) d <>
        renderAttrs [("label", doubleQuote $ fromDisp v)]


main :: IO ()
main = do
    pkgs <- getArgs
    home <- getHomeDirectory
    give (CabalInstall "cabal")
        $ give (IndexFile $ home </> ".cabal/packages/hackage.haskell.org/00-index.tar.gz")
        $ give (CabalConfig [] C.buildPlatform C.buildCompilerId)
        $ give (DotConfig "dependency")
        $ withTempDirectory
        $ withSandbox $ do
            createDepGraph pkgs >>= TL.putStrLn . B.toLazyText . renderDot
