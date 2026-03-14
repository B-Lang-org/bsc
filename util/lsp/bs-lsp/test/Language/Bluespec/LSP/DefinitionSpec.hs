-- | Tests for go-to-definition functionality.
module Language.Bluespec.LSP.DefinitionSpec (spec) where

import Test.Hspec
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension, takeBaseName)
import Control.Monad (forM_, filterM)
import Data.Maybe (catMaybes, listToMaybe)
import Data.List (sortOn)

import Language.LSP.Protocol.Types (Position(..), Location(..), Range(..), Uri(..))

import Language.Bluespec.Parser (parsePackage)
import Language.Bluespec.Position (SrcSpan(..))
import qualified Language.Bluespec.Position as Pos
import Language.Bluespec.LSP.SymbolTable (buildSymbolTable, SymbolTable, loadPreludeSymbolTable, discoverPreludeFilePath, getAllSymbols, Symbol(..), SymbolKind(..), LibrarySearchResult(..), discoverLibrariesDirWithDebug, discoverLibrariesDir, formatLibrarySearchError)
import Language.Bluespec.LSP.Definition (getDefinition, getDefinitionCrossFile)
import Language.Bluespec.LSP.Util (getIdentifierAtPosition)
import Language.Bluespec.LSP.State (emptyServerState, updateModuleIndex, ModuleInfo(..), setPreludeSymbols)
import Language.Bluespec.LSP.TypeEnv (emptyTypeEnv)

-- | Recursively find all .bs files in a directory.
findBsFiles :: FilePath -> IO [FilePath]
findBsFiles dir = do
  entries <- listDirectory dir
  let fullPaths = map (dir </>) entries
  files <- filterM doesFileExist fullPaths
  dirs <- filterM doesDirectoryExist fullPaths
  let bsFiles = filter (\f -> takeExtension f == ".bs") files
  subFiles <- concat <$> mapM findBsFiles dirs
  pure (bsFiles ++ subFiles)

-- | Load a .bs file and build its symbol table.
-- Returns (filePath, source, symbolTable) or Nothing if parsing fails.
loadBsFile :: FilePath -> IO (Maybe (FilePath, Text, SymbolTable))
loadBsFile path = do
  contents <- TIO.readFile path
  case parsePackage (T.pack path) contents of
    Left _ -> pure Nothing
    Right pkg -> pure $ Just (path, contents, buildSymbolTable pkg)

-- | Helper to create a position (0-indexed as LSP uses).
pos :: Int -> Int -> Position
pos line col = Position (fromIntegral line) (fromIntegral col)

-- | Extract line number from a Location (convert back to 0-indexed).
locLine :: Location -> Int
locLine loc = fromIntegral $ _line $ _start $ _range loc

-- | Extract column number from a Location (convert back to 0-indexed).
locCol :: Location -> Int
locCol loc = fromIntegral $ _character $ _start $ _range loc

-- | Get the symbol name at a location by reading from source.
-- This extracts the identifier at the returned position to verify we got the right symbol.
getSymbolNameAtLocation :: Text -> Location -> Maybe Text
getSymbolNameAtLocation src loc =
  let line = locLine loc
      col = locCol loc
  in getIdentifierAtPosition src (pos line col)

-- | Parse source and build symbol table.
parseAndBuildSymbols :: Text -> Either String SymbolTable
parseAndBuildSymbols src = parseAndBuildSymbolsWithName "test.bs" src

-- | Parse source with a specific filename and build symbol table.
parseAndBuildSymbolsWithName :: Text -> Text -> Either String SymbolTable
parseAndBuildSymbolsWithName filename src = case parsePackage filename src of
  Left err -> Left $ show err
  Right pkg -> Right $ buildSymbolTable pkg

-- | Simple Bluespec source with a function definition and usage.
simpleFunctionSource :: Text
simpleFunctionSource = T.unlines
  [ "package Test where"                     -- line 0
  , ""                                       -- line 1
  , "addOne :: Integer -> Integer"           -- line 2
  , "addOne x = x + 1"                       -- line 3
  , ""                                       -- line 4
  , "addTwo :: Integer -> Integer"           -- line 5
  , "addTwo x = addOne (addOne x)"           -- line 6
  --            ^col 11 (usage of addOne)
  ]

-- | Source with type definition and usage.
typeUsageSource :: Text
typeUsageSource = T.unlines
  [ "package Test where"                     -- line 0
  , ""                                       -- line 1
  , "type MyInt = Integer"                   -- line 2
  --     ^col 5 (definition of MyInt)
  , ""                                       -- line 3
  , "double :: MyInt -> MyInt"               -- line 4
  --           ^col 10 (usage of MyInt)
  , "double x = x + x"                       -- line 5
  ]

-- | Source with data type and constructor usage.
dataConstructorSource :: Text
dataConstructorSource = T.unlines
  [ "package Test where"                     -- line 0
  , ""                                       -- line 1
  , "data Maybe a = Just a | Nothing"        -- line 2
  --                ^col 15 (Just constructor definition)
  , ""                                       -- line 3
  , "wrap :: a -> Maybe a"                   -- line 4
  , "wrap x = Just x"                        -- line 5
  --         ^col 9 (usage of Just)
  ]

-- | Source with interface field usage.
interfaceFieldSource :: Text
interfaceFieldSource = T.unlines
  [ "package Test where"                     -- line 0
  , ""                                       -- line 1
  , "interface Counter ="                    -- line 2
  , "  inc :: Action"                        -- line 3
  --  ^col 2 (definition of inc)
  , "  get :: Integer"                       -- line 4
  , ""                                       -- line 5
  , "useCounter :: Counter -> Action"        -- line 6
  , "useCounter c = c.inc"                   -- line 7
  --                  ^col 17 (usage of inc - this is tricky, it's a field access)
  ]

-- | Source with nested scope - let binding uses outer parameter.
nestedScopeSource :: Text
nestedScopeSource = T.unlines
  [ "package Test where"                     -- line 0
  , ""                                       -- line 1
  , "outer :: Integer -> Integer"            -- line 2
  , "outer x ="                              -- line 3
  --      ^col 6 (definition of x)
  , "  let inner y = x + y"                  -- line 4
  --      ^col 6 (definition of inner)
  --            ^col 12 (definition of y)
  --                ^col 16 (usage of x - should find line 3 col 6)
  --                    ^col 20 (usage of y - should find line 4 col 12)
  , "  in inner 1"                           -- line 5
  --     ^col 5 (usage of inner)
  ]

-- | Source with shadowing - inner binding shadows outer parameter.
shadowingScopeSource :: Text
shadowingScopeSource = T.unlines
  [ "package Test where"                     -- line 0
  , ""                                       -- line 1
  , "outer :: Integer -> Integer"            -- line 2
  , "outer x ="                              -- line 3
  --      ^col 6 (definition of outer's x)
  , "  let inner x = x + 1"                  -- line 4
  --            ^col 12 (definition of inner's x - shadows outer's x)
  --                ^col 16 (usage of x - should find line 4 col 12, the shadowing one)
  , "  in inner x"                           -- line 5
  --            ^col 11 (usage of x - should find line 3 col 6, outer's x)
  ]

spec :: Spec
spec = do
  describe "getIdentifierAtPosition" $ do
    it "extracts identifier when cursor is at start of identifier" $ do
      let src = "hello world"
      getIdentifierAtPosition src (pos 0 0) `shouldBe` Just "hello"

    it "extracts identifier when cursor is in middle of identifier" $ do
      let src = "hello world"
      getIdentifierAtPosition src (pos 0 2) `shouldBe` Just "hello"

    it "extracts identifier when cursor is at end of identifier" $ do
      let src = "hello world"
      getIdentifierAtPosition src (pos 0 4) `shouldBe` Just "hello"

    it "extracts second identifier on line" $ do
      let src = "hello world"
      getIdentifierAtPosition src (pos 0 6) `shouldBe` Just "world"

    it "returns Nothing when cursor is on whitespace" $ do
      let src = "hello world"
      getIdentifierAtPosition src (pos 0 5) `shouldBe` Nothing

    it "handles identifiers with underscores" $ do
      let src = "my_function test"
      getIdentifierAtPosition src (pos 0 3) `shouldBe` Just "my_function"

    it "handles identifiers with apostrophes" $ do
      let src = "x' = x + 1"
      getIdentifierAtPosition src (pos 0 0) `shouldBe` Just "x'"

    it "handles identifiers with digits" $ do
      let src = "var123 = 0"
      getIdentifierAtPosition src (pos 0 3) `shouldBe` Just "var123"

    it "returns Nothing for out of bounds line" $ do
      let src = "hello"
      getIdentifierAtPosition src (pos 5 0) `shouldBe` Nothing

    it "returns Nothing for out of bounds column" $ do
      let src = "hello"
      getIdentifierAtPosition src (pos 0 10) `shouldBe` Nothing

    it "extracts identifier on specific line in multi-line source" $ do
      let src = T.unlines ["line0", "line1", "line2"]
      getIdentifierAtPosition src (pos 1 0) `shouldBe` Just "line1"

    it "returns Nothing when cursor is on operator" $ do
      let src = "x + y"
      getIdentifierAtPosition src (pos 0 2) `shouldBe` Nothing

  describe "getDefinition" $ do
    describe "on definition sites" $ do
      it "finds function definition when cursor is on the definition name" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "addOne" at line 3, col 0 (the definition)
            let result = getDefinition st simpleFunctionSource (pos 3 0)
            case result of
              Nothing -> expectationFailure "Expected to find definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 3
                -- Verify we got the correct symbol by checking the name at the returned location
                getSymbolNameAtLocation simpleFunctionSource loc `shouldBe` Just "addOne"

      it "finds type definition when cursor is on the definition name" $ do
        case parseAndBuildSymbols typeUsageSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "MyInt" at line 2, col 5 (the definition)
            let result = getDefinition st typeUsageSource (pos 2 5)
            case result of
              Nothing -> expectationFailure "Expected to find definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAtLocation typeUsageSource loc `shouldBe` Just "MyInt"

    describe "on usage sites" $ do
      it "finds function definition when cursor is on a function call" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "addOne" at line 6, col 11 (a usage/call site)
            -- This should navigate to line 3 where addOne is defined
            let result = getDefinition st simpleFunctionSource (pos 6 11)
            case result of
              Nothing -> expectationFailure "Expected to find definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 3
                -- Critically verify we got the right symbol, not just any symbol on line 3
                getSymbolNameAtLocation simpleFunctionSource loc `shouldBe` Just "addOne"

      it "finds type definition when cursor is on a type usage" $ do
        case parseAndBuildSymbols typeUsageSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "MyInt" at line 4, col 10 (usage in type signature)
            -- This should navigate to line 2 where MyInt is defined
            let result = getDefinition st typeUsageSource (pos 4 10)
            case result of
              Nothing -> expectationFailure "Expected to find definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAtLocation typeUsageSource loc `shouldBe` Just "MyInt"

      it "finds data constructor definition when cursor is on constructor usage" $ do
        case parseAndBuildSymbols dataConstructorSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "Just" at line 5, col 9 (usage in expression)
            -- This should navigate to line 2 where Just is defined
            let result = getDefinition st dataConstructorSource (pos 5 9)
            case result of
              Nothing -> expectationFailure "Expected to find definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAtLocation dataConstructorSource loc `shouldBe` Just "Just"

      it "finds second usage of function on same line" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 6: "addTwo x = addOne (addOne x)"
            --                     ^col 11    ^col 19
            -- Test the SECOND occurrence of addOne at col 19
            let result = getDefinition st simpleFunctionSource (pos 6 19)
            case result of
              Nothing -> expectationFailure "Expected to find definition for second addOne usage but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 3
                locCol loc `shouldBe` 0  -- Definition starts at column 0
                getSymbolNameAtLocation simpleFunctionSource loc `shouldBe` Just "addOne"

      it "verifies exact column position of returned definition" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Look up addOne, should return exact position of definition
            let result = getDefinition st simpleFunctionSource (pos 6 11)
            case result of
              Nothing -> expectationFailure "Expected to find definition but got Nothing"
              Just loc -> do
                -- Should point to start of "addOne" on line 3, col 0
                locLine loc `shouldBe` 3
                locCol loc `shouldBe` 0

      it "finds interface field definition from field access" $ do
        case parseAndBuildSymbols interfaceFieldSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 7: "useCounter c = c.inc"
            --                          ^col 17 is on "inc"
            let result = getDefinition st interfaceFieldSource (pos 7 17)
            case result of
              Nothing -> expectationFailure "Expected to find interface field definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 3  -- "inc :: Action" is on line 3
                getSymbolNameAtLocation interfaceFieldSource loc `shouldBe` Just "inc"

      it "finds parameter definition when cursor is on parameter usage" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 3: "addOne x = x + 1"
            --                ^col 7 is definition of x
            --                    ^col 11 is usage of x
            let result = getDefinition st simpleFunctionSource (pos 3 11)
            case result of
              Nothing -> expectationFailure "Expected to find parameter definition but got Nothing"
              Just loc -> do
                -- Should point to the parameter definition at col 7
                locLine loc `shouldBe` 3
                locCol loc `shouldBe` 7
                getSymbolNameAtLocation simpleFunctionSource loc `shouldBe` Just "x"

      it "finds Nothing constructor definition" $ do
        case parseAndBuildSymbols dataConstructorSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 2: "data Maybe a = Just a | Nothing"
            --                                 ^col 24 is "Nothing"
            -- Look up Nothing by clicking on it at the definition
            let result = getDefinition st dataConstructorSource (pos 2 24)
            case result of
              Nothing -> expectationFailure "Expected to find Nothing constructor but got Nothing (ironic)"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAtLocation dataConstructorSource loc `shouldBe` Just "Nothing"

      it "finds type variable definition" $ do
        case parseAndBuildSymbols dataConstructorSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 2: "data Maybe a = Just a | Nothing"
            --                    ^col 11 is definition of type var 'a'
            --                         ^col 20 is usage of type var 'a'
            let result = getDefinition st dataConstructorSource (pos 2 20)
            case result of
              Nothing -> expectationFailure "Expected to find type variable definition but got Nothing"
              Just loc -> do
                -- Should point to the type variable definition at col 11
                locLine loc `shouldBe` 2
                locCol loc `shouldBe` 11
                getSymbolNameAtLocation dataConstructorSource loc `shouldBe` Just "a"

      it "distinguishes between same-named symbols in different functions" $ do
        -- This tests that parameter 'x' in addOne is different from 'x' in addTwo
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 6: "addTwo x = addOne (addOne x)"
            --                ^col 7 is addTwo's x parameter definition
            --                                  ^col 26 is usage of addTwo's x
            let result = getDefinition st simpleFunctionSource (pos 6 26)
            case result of
              Nothing -> expectationFailure "Expected to find parameter definition but got Nothing"
              Just loc -> do
                -- Should point to addTwo's x parameter at line 6, col 7
                -- NOT to addOne's x parameter at line 3
                locLine loc `shouldBe` 6
                locCol loc `shouldBe` 7
                getSymbolNameAtLocation simpleFunctionSource loc `shouldBe` Just "x"

      it "finds outer parameter from nested let binding (ancestral scope)" $ do
        -- This tests that 'x' used inside 'inner' resolves to outer's parameter
        case parseAndBuildSymbols nestedScopeSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 4: "  let inner y = x + y"
            --                        ^col 16 is usage of x (outer's parameter)
            let result = getDefinition st nestedScopeSource (pos 4 16)
            case result of
              Nothing -> expectationFailure "Expected to find parameter definition but got Nothing"
              Just loc -> do
                -- Should point to outer's x parameter at line 3, col 6
                locLine loc `shouldBe` 3
                locCol loc `shouldBe` 6
                getSymbolNameAtLocation nestedScopeSource loc `shouldBe` Just "x"

      it "finds shadowing variable when inner scope shadows outer" $ do
        -- This tests that 'x' used inside 'inner' resolves to inner's x (the shadowing one)
        case parseAndBuildSymbols shadowingScopeSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 4: "  let inner x = x + 1"
            --                        ^col 16 is usage of x (should be inner's x)
            let result = getDefinition st shadowingScopeSource (pos 4 16)
            case result of
              Nothing -> expectationFailure "Expected to find parameter definition but got Nothing"
              Just loc -> do
                -- Should point to inner's x at line 4, col 12 (the shadowing binding)
                locLine loc `shouldBe` 4
                locCol loc `shouldBe` 12
                getSymbolNameAtLocation shadowingScopeSource loc `shouldBe` Just "x"

      it "finds outer variable when outside inner scope" $ do
        -- This tests that 'x' used outside 'inner' resolves to outer's x
        case parseAndBuildSymbols shadowingScopeSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 5: "  in inner x"
            --                    ^col 11 is usage of x (should be outer's x)
            let result = getDefinition st shadowingScopeSource (pos 5 11)
            case result of
              Nothing -> expectationFailure "Expected to find parameter definition but got Nothing"
              Just loc -> do
                -- Should point to outer's x at line 3, col 6
                locLine loc `shouldBe` 3
                locCol loc `shouldBe` 6
                getSymbolNameAtLocation shadowingScopeSource loc `shouldBe` Just "x"

    describe "edge cases" $ do
      it "returns Nothing when cursor is on whitespace" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on empty line 1
            let result = getDefinition st simpleFunctionSource (pos 1 0)
            result `shouldBe` Nothing

      it "returns Nothing when cursor is on a keyword" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "package" keyword at line 0, col 0
            -- "package" is a keyword, not an identifier, so no definition should be found
            let result = getDefinition st simpleFunctionSource (pos 0 0)
            -- The implementation extracts "package" as an identifier and looks it up.
            -- Since "package" is not defined as a symbol, this should return Nothing.
            result `shouldBe` Nothing

      it "finds package name when cursor is on package name" $ do
        case parseAndBuildSymbols simpleFunctionSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Cursor on "Test" (package name) at line 0, col 8
            -- "package Test where" - "Test" starts at col 8
            let result = getDefinition st simpleFunctionSource (pos 0 8)
            case result of
              Nothing -> expectationFailure "Expected to find package name definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 0
                getSymbolNameAtLocation simpleFunctionSource loc `shouldBe` Just "Test"

    describe "cross-file definition lookup" $ do
      it "finds function definition in imported module" $ do
        -- Set up: LibModule defines 'helper', MainModule imports and uses it
        -- Important: parse each module with its correct filename so symbols have correct spans
        let libResult = parseAndBuildSymbolsWithName "/workspace/LibModule.bs" libModuleSource
            mainResult = parseAndBuildSymbolsWithName "/workspace/MainModule.bs" mainModuleSource
        case (libResult, mainResult) of
          (Left err, _) -> expectationFailure $ "LibModule parse failed: " ++ err
          (_, Left err) -> expectationFailure $ "MainModule parse failed: " ++ err
          (Right libSt, Right mainSt) -> do
            -- Build server state with LibModule indexed
            let libInfo = ModuleInfo
                  { miFilePath = "/workspace/LibModule.bs"
                  , miSymbols = libSt
                  , miTypeEnv = emptyTypeEnv
                  , miParsed = either (const Nothing) Just (parsePackage "/workspace/LibModule.bs" libModuleSource)
                  }
                serverState = updateModuleIndex "LibModule" libInfo emptyServerState

            -- Look up 'helper' at line 5, col 11 in MainModule (usage site)
            -- This should find the definition in LibModule at line 3
            let result = getDefinitionCrossFile serverState emptyTypeEnv mainSt mainModuleSource (pos 5 11)
            case result of
              Nothing -> expectationFailure "Expected to find cross-file definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 3  -- 'helper' is defined on line 3 of LibModule
                -- Verify the symbol name at the returned location
                getSymbolNameAtLocation libModuleSource loc `shouldBe` Just "helper"
                -- Check that the URI points exactly to the library module
                let Uri uri = _uri loc
                uri `shouldBe` "file:///workspace/LibModule.bs"

      it "finds type definition in imported module" $ do
        let libResult = parseAndBuildSymbolsWithName "/workspace/LibModule.bs" libModuleSource
            mainResult = parseAndBuildSymbolsWithName "/workspace/MainModule.bs" mainModuleSource
        case (libResult, mainResult) of
          (Left err, _) -> expectationFailure $ "LibModule parse failed: " ++ err
          (_, Left err) -> expectationFailure $ "MainModule parse failed: " ++ err
          (Right libSt, Right mainSt) -> do
            let libInfo = ModuleInfo
                  { miFilePath = "/workspace/LibModule.bs"
                  , miSymbols = libSt
                  , miTypeEnv = emptyTypeEnv
                  , miParsed = either (const Nothing) Just (parsePackage "/workspace/LibModule.bs" libModuleSource)
                  }
                serverState = updateModuleIndex "LibModule" libInfo emptyServerState

            -- Look up 'LibType' at line 7, col 11 in MainModule (usage in type signature)
            -- This should find the definition in LibModule at line 5
            let result = getDefinitionCrossFile serverState emptyTypeEnv mainSt mainModuleSource (pos 7 11)
            case result of
              Nothing -> expectationFailure "Expected to find cross-file type definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 5  -- 'LibType' is defined on line 5 of LibModule
                getSymbolNameAtLocation libModuleSource loc `shouldBe` Just "LibType"
                let Uri uri = _uri loc
                uri `shouldBe` "file:///workspace/LibModule.bs"

      it "prefers local definition over imported when both exist" $ do
        let libResult = parseAndBuildSymbolsWithName "/workspace/LibModule.bs" libModuleSource
            mainResult = parseAndBuildSymbolsWithName "/workspace/MainWithLocal.bs" mainWithLocalSource
        case (libResult, mainResult) of
          (Left err, _) -> expectationFailure $ "LibModule parse failed: " ++ err
          (_, Left err) -> expectationFailure $ "MainWithLocal parse failed: " ++ err
          (Right libSt, Right mainSt) -> do
            let libInfo = ModuleInfo
                  { miFilePath = "/workspace/LibModule.bs"
                  , miSymbols = libSt
                  , miTypeEnv = emptyTypeEnv
                  , miParsed = either (const Nothing) Just (parsePackage "/workspace/LibModule.bs" libModuleSource)
                  }
                serverState = updateModuleIndex "LibModule" libInfo emptyServerState

            -- Look up 'helper' at line 8, col 9 in MainWithLocal
            -- This should find the LOCAL definition at line 5, not the imported one
            let result = getDefinitionCrossFile serverState emptyTypeEnv mainSt mainWithLocalSource (pos 8 9)
            case result of
              Nothing -> expectationFailure "Expected to find local definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 5  -- Local 'helper' is defined on line 5
                getSymbolNameAtLocation mainWithLocalSource loc `shouldBe` Just "helper"
                -- Should point to MainWithLocal, NOT LibModule
                let Uri uri = _uri loc
                uri `shouldBe` "file:///workspace/MainWithLocal.bs"

      it "returns Nothing for symbol not in any module" $ do
        let libResult = parseAndBuildSymbolsWithName "/workspace/LibModule.bs" libModuleSource
        case libResult of
          Left err -> expectationFailure $ "LibModule parse failed: " ++ err
          Right libSt -> do
            let libInfo = ModuleInfo
                  { miFilePath = "/workspace/LibModule.bs"
                  , miSymbols = libSt
                  , miTypeEnv = emptyTypeEnv
                  , miParsed = either (const Nothing) Just (parsePackage "/workspace/LibModule.bs" libModuleSource)
                  }
                serverState = updateModuleIndex "LibModule" libInfo emptyServerState

            -- Create source with unknown symbol
            let unknownSource = T.unlines
                  [ "package Unknown where"
                  , "import LibModule"
                  , ""
                  , "test = unknownFunction 1"
                  ]
            case parseAndBuildSymbolsWithName "/workspace/Unknown.bs" unknownSource of
              Left err -> expectationFailure $ "Unknown source parse failed: " ++ err
              Right unknownSt -> do
                -- Look up 'unknownFunction' - should not be found anywhere
                let result = getDefinitionCrossFile serverState emptyTypeEnv unknownSt unknownSource (pos 3 7)
                result `shouldBe` Nothing

    describe "standard library definitions" $ do
      it "discovers and parses all standard library .bs files" $ do
        searchResult <- discoverLibrariesDirWithDebug
        case searchResult of
          LibraryNotFound _ ->
            pendingWith "standard library not discoverable in this environment (set BLUESPEC_SRC or BLUESPECDIR)"
          LibraryFound libDir -> do
            -- Find all .bs files in the library
            bsFiles <- findBsFiles libDir
            bsFiles `shouldSatisfy` (not . null)  -- Should find at least some files

            -- Try to parse each file and count successes/failures
            results <- mapM loadBsFile bsFiles
            let loaded = catMaybes results
                failedCount = length bsFiles - length loaded

            -- Report what we found
            -- At least 50% of files should parse successfully
            -- (some may have syntax we don't support yet)
            let successRate = fromIntegral (length loaded) / fromIntegral (length bsFiles) :: Double
            successRate `shouldSatisfy` (>= 0.5)

            -- Verify we loaded some important files
            let loadedNames = map (\(p, _, _) -> takeBaseName p) loaded
            loadedNames `shouldSatisfy` (\names -> "Prelude" `elem` names)

      it "returns locations pointing to the actual loaded file, not a different copy" $ do
        searchResult <- discoverLibrariesDirWithDebug
        case searchResult of
          LibraryNotFound _ ->
            pendingWith "standard library not discoverable in this environment (set BLUESPEC_SRC or BLUESPECDIR)"
          LibraryFound libDir -> do
            -- Find and load all .bs files
            bsFiles <- findBsFiles libDir
            results <- mapM loadBsFile bsFiles
            let loaded = catMaybes results

            -- For each loaded file, pick a symbol and verify lookup returns
            -- a location pointing to THAT EXACT FILE
            forM_ loaded $ \(filePath, source, symbolTable) -> do
              let symbols = getAllSymbols symbolTable
                  -- Pick a good symbol to test (prefer types/functions over parameters)
                  goodSymbols = filter isGoodSymbol symbols
                  mTestSymbol = listToMaybe $ sortOn symName goodSymbols

              case mTestSymbol of
                Nothing -> pure ()  -- Skip files with no good symbols
                Just testSym -> do
                  -- Look up this symbol in its own file
                  let result = getDefinition symbolTable source (spanToPosition (symSpan testSym))
                  case result of
                    Nothing ->
                      expectationFailure $ "Failed to find symbol '" ++ T.unpack (symName testSym)
                        ++ "' in " ++ filePath
                    Just loc -> do
                      -- CRITICAL: Verify the URI points to the EXACT file we loaded
                      let Uri uri = _uri loc
                          expectedUri = "file://" <> T.pack filePath
                      uri `shouldBe` expectedUri

      it "looks up symbols from standard library when used in user code" $ do
        searchResult <- discoverLibrariesDirWithDebug
        case searchResult of
          LibraryNotFound _ ->
            pendingWith "standard library not discoverable in this environment (set BLUESPEC_SRC or BLUESPECDIR)"
          LibraryFound libDir -> do
            -- Find and load Prelude specifically
            bsFiles <- findBsFiles libDir
            results <- mapM loadBsFile bsFiles
            let loaded = catMaybes results
                mPrelude = listToMaybe [(p, s, st) | (p, s, st) <- loaded, takeBaseName p == "Prelude"]

            case mPrelude of
              Nothing -> expectationFailure "Could not load Prelude.bs"
              Just (preludePath, preludeSource, preludeSt) -> do
                -- Find a type defined in Prelude to test
                let symbols = getAllSymbols preludeSt
                    typeSymbols = filter (\s -> symKind s `elem` [SKType, SKData, SKClass]) symbols
                    -- Pick "Integer" if available, otherwise first type
                    mTestType = listToMaybe $ filter (\s -> symName s == "Integer") typeSymbols
                               ++ typeSymbols

                case mTestType of
                  Nothing -> expectationFailure "Prelude has no type definitions to test"
                  Just testType -> do
                    let typeName = symName testType
                    -- Create user code that uses this type
                    let userSource = T.unlines
                          [ "package UserCode where"
                          , ""
                          , "myFunc :: " <> typeName <> " -> " <> typeName
                          , "myFunc x = x"
                          ]
                    case parseAndBuildSymbolsWithName "/workspace/UserCode.bs" userSource of
                      Left err -> expectationFailure $ "Failed to parse user code: " ++ err
                      Right userSt -> do
                        -- Set up server state with prelude
                        let serverState = setPreludeSymbols (Just preludeSt) emptyServerState

                        -- Look up the type at line 2, col 10 (where the type name starts in signature)
                        let typeCol = 10  -- "myFunc :: " is 10 chars
                        let result = getDefinitionCrossFile serverState emptyTypeEnv userSt userSource (pos 2 typeCol)
                        case result of
                          Nothing -> expectationFailure $
                            "Failed to find definition for '" ++ T.unpack typeName ++ "'"
                          Just loc -> do
                            -- Verify it points to the PRELUDE file we loaded
                            let Uri uri = _uri loc
                                expectedUri = "file://" <> T.pack preludePath
                            uri `shouldBe` expectedUri
                            -- Verify the symbol name at that location
                            getSymbolNameAtLocation preludeSource loc `shouldBe` Just typeName

    describe "module expression definitions" $ do
      it "finds variable bound inside module expression" $ do
        case parseAndBuildSymbols moduleExprSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 10: "    inc = count := count + 1"
            --                    ^col 10 is usage of 'count'
            -- Should find 'count' definition at line 8, col 2
            let result = getDefinition st moduleExprSource (pos 10 10)
            case result of
              Nothing -> expectationFailure "Expected to find 'count' definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 8
                locCol loc `shouldBe` 2
                getSymbolNameAtLocation moduleExprSource loc `shouldBe` Just "count"

      it "finds variable from second usage inside module expression" $ do
        case parseAndBuildSymbols moduleExprSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- Line 11: "    get = count"
            --                    ^col 10 is usage of 'count'
            -- Should find 'count' definition at line 8, col 2
            let result = getDefinition st moduleExprSource (pos 11 10)
            case result of
              Nothing -> expectationFailure "Expected to find 'count' definition but got Nothing"
              Just loc -> do
                locLine loc `shouldBe` 8
                locCol loc `shouldBe` 2
                getSymbolNameAtLocation moduleExprSource loc `shouldBe` Just "count"

  where
    isGoodSymbol sym = symKind sym `elem` [SKType, SKData, SKFunction, SKInterface, SKClass]

    spanToPosition srcSpan =
      let line = fromIntegral (Pos.posLine (spanBegin srcSpan)) - 1  -- Convert to 0-indexed
          col = fromIntegral (Pos.posColumn (spanBegin srcSpan)) - 1
      in pos line col

-- | Library module that exports some definitions.
-- Line 0: "package LibModule where"
-- Line 1: ""
-- Line 2: "helper :: Integer -> Integer"
-- Line 3: "helper x = x * 2"  <- definition of helper at col 0
-- Line 4: ""
-- Line 5: "type LibType = Integer"  <- definition of LibType at col 5
libModuleSource :: Text
libModuleSource = T.unlines
  [ "package LibModule where"
  , ""
  , "helper :: Integer -> Integer"
  , "helper x = x * 2"
  , ""
  , "type LibType = Integer"
  ]

-- | Main module that imports and uses LibModule.
-- Line 0: "package MainModule where"
-- Line 1: ""
-- Line 2: "import LibModule"
-- Line 3: ""
-- Line 4: "double :: Integer -> Integer"
-- Line 5: "double x = helper x"  <- usage of helper at col 11
-- Line 6: ""
-- Line 7: "useType :: LibType -> LibType"  <- usage of LibType at col 11
-- Line 8: "useType t = t"
mainModuleSource :: Text
mainModuleSource = T.unlines
  [ "package MainModule where"
  , ""
  , "import LibModule"
  , ""
  , "double :: Integer -> Integer"
  , "double x = helper x"
  , ""
  , "useType :: LibType -> LibType"
  , "useType t = t"
  ]

-- | Main module with local definition that shadows import.
-- Line 0: "package MainWithLocal where"
-- Line 1: ""
-- Line 2: "import LibModule"
-- Line 3: ""
-- Line 4: "helper :: Integer -> Integer"
-- Line 5: "helper x = x + 1"  <- LOCAL definition of helper
-- Line 6: ""
-- Line 7: "test :: Integer -> Integer"
-- Line 8: "test x = helper x"  <- usage at col 9, should resolve to LOCAL helper
mainWithLocalSource :: Text
mainWithLocalSource = T.unlines
  [ "package MainWithLocal where"
  , ""
  , "import LibModule"
  , ""
  , "helper :: Integer -> Integer"
  , "helper x = x + 1"
  , ""
  , "test :: Integer -> Integer"
  , "test x = helper x"
  ]

-- | Module expression test source.
-- Line 0: "package ModuleExprTest where"
-- Line 1: ""
-- Line 2: "interface Counter ="
-- Line 3: "  inc :: Action"
-- Line 4: "  get :: Integer"
-- Line 5: ""
-- Line 6: "mkCounter :: Module Counter"
-- Line 7: "mkCounter = module"
-- Line 8: "  count <- mkReg 0"         <- 'count' binding at col 2
-- Line 9: "  interface Counter"
-- Line 10: "    inc = count := count + 1"  <- 'inc' field at col 4, 'count' usage at col 10
-- Line 11: "    get = count"               <- 'get' field at col 4, 'count' usage at col 10
moduleExprSource :: Text
moduleExprSource = T.unlines
  [ "package ModuleExprTest where"
  , ""
  , "interface Counter ="
  , "  inc :: Action"
  , "  get :: Integer"
  , ""
  , "mkCounter :: Module Counter"
  , "mkCounter = module"
  , "  count <- mkReg 0"
  , "  interface Counter"
  , "    inc = count := count + 1"
  , "    get = count"
  ]
