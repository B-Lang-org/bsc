-- | Tests for go-to-definition functionality in BSV (.bsv) files.
module Language.Bluespec.LSP.BsvDefinitionSpec (spec) where

import Test.Hspec
import Data.Text (Text)
import qualified Data.Text as T

import Language.LSP.Protocol.Types (Position(..), Location(..), Range(..), Uri(..))

import Language.Bluespec.BSV.Parser (parseBSVPackage)
import Language.Bluespec.LSP.SymbolTable (buildSymbolTable, SymbolTable)
import Language.Bluespec.LSP.Definition (getDefinition)
import Language.Bluespec.LSP.Util (getIdentifierAtPosition)

-- | Helper to create a position (0-indexed as LSP uses).
pos :: Int -> Int -> Position
pos line col = Position (fromIntegral line) (fromIntegral col)

-- | Extract line number from a Location (0-indexed).
locLine :: Location -> Int
locLine loc = fromIntegral $ _line $ _start $ _range loc

-- | Extract column number from a Location (0-indexed).
locCol :: Location -> Int
locCol loc = fromIntegral $ _character $ _start $ _range loc

-- | Get the symbol name at a location.
getSymbolNameAt :: Text -> Location -> Maybe Text
getSymbolNameAt src loc = getIdentifierAtPosition src (pos (locLine loc) (locCol loc))

-- | Parse BSV source and build symbol table.
parseAndBuild :: Text -> Text -> Either String SymbolTable
parseAndBuild filename src = case parseBSVPackage filename src of
  Left err -> Left $ show err
  Right pkg -> Right $ buildSymbolTable pkg

-- ---------------------------------------------------------------------------
-- Test sources
-- ---------------------------------------------------------------------------

-- | Simple BSV interface and module.
-- line 0: package BsvTest;
-- line 1: (blank)
-- line 2: interface IFoo;                   <- interface IFoo defined here
-- line 3:   method Action setVal(Bit#(8) x); <- setVal defined here
-- line 4:   method Bit#(8) getVal();         <- getVal defined here
-- line 5: endinterface
-- line 6: (blank)
-- line 7: module mkFoo(IFoo);               <- mkFoo defined here
-- line 8:   Reg#(Bit#(8)) r <- mkReg(0);    <- r defined here
-- line 9:   method Action setVal(Bit#(8) x); <- setVal method impl
-- line 10:    r <= x;
-- line 11:  endmethod
-- line 12:  method Bit#(8) getVal();          <- getVal method impl
-- line 13:    return r;
-- line 14:  endmethod
-- line 15: endmodule
-- line 16: endpackage
bsvSimpleSource :: Text
bsvSimpleSource = T.unlines
  [ "package BsvTest;"                          -- 0
  , ""                                          -- 1
  , "interface IFoo;"                           -- 2
  , "  method Action setVal(Bit#(8) x);"       -- 3
  , "  method Bit#(8) getVal();"               -- 4
  , "endinterface"                             -- 5
  , ""                                          -- 6
  , "module mkFoo(IFoo);"                       -- 7
  , "  Reg#(Bit#(8)) r <- mkReg(0);"           -- 8
  , "  method Action setVal(Bit#(8) x);"       -- 9
  , "    r <= x;"                              -- 10
  , "  endmethod"                              -- 11
  , "  method Bit#(8) getVal();"               -- 12
  , "    return r;"                            -- 13
  , "  endmethod"                              -- 14
  , "endmodule"                                -- 15
  , "endpackage"                               -- 16
  ]

-- | BSV source with typedef and function.
-- line 0: package BsvTypes;
-- line 1: (blank)
-- line 2: typedef UInt#(8) MyByte;          <- MyByte defined
-- line 3: (blank)
-- line 4: function MyByte increment(MyByte x);  <- increment defined, MyByte used
-- line 5:   return x + 1;
-- line 6: endfunction
-- line 7: endpackage
bsvTypedefSource :: Text
bsvTypedefSource = T.unlines
  [ "package BsvTypes;"           -- 0
  , ""                            -- 1
  , "typedef UInt#(8) MyByte;"   -- 2
  , ""                            -- 3
  , "function MyByte increment(MyByte x);"  -- 4
  , "  return x + 1;"            -- 5
  , "endfunction"                 -- 6
  , "endpackage"                  -- 7
  ]

-- | BSV source with ternary expressions.
-- line 0: package BsvTernary;
-- line 1: (blank)
-- line 2: function Bit#(2) chooseMxl(Bool is32);  <- chooseMxl defined
-- line 3:   return (is32 ? 2'b01 : 2'b10);        <- ternary expression
-- line 4: endfunction
-- line 5: endpackage
bsvTernarySource :: Text
bsvTernarySource = T.unlines
  [ "package BsvTernary;"                         -- 0
  , ""                                             -- 1
  , "function Bit#(2) chooseMxl(Bool is32);"      -- 2
  , "  return (is32 ? 2'b01 : 2'b10);"           -- 3
  , "endfunction"                                 -- 4
  , "endpackage"                                  -- 5
  ]

-- | BSV source with enum typedef.
-- line 0: package BsvEnum;
-- line 1: (blank)
-- line 2: typedef enum { Red, Green, Blue } Color deriving (Bits, Eq);
-- line 3: (blank)
-- line 4: function Color nextColor(Color c);   <- nextColor defined, Color used (col 16)
-- line 5:   case (c)                           <- c used
-- line 6:     Red:   return Green;             <- Red, Green used
-- line 7:     Green: return Blue;              <- Green, Blue used
-- line 8:     Blue:  return Red;               <- Blue, Red used
-- line 9:   endcase
-- line 10: endfunction
-- line 11: endpackage
bsvEnumSource :: Text
bsvEnumSource = T.unlines
  [ "package BsvEnum;"                                              -- 0
  , ""                                                              -- 1
  , "typedef enum { Red, Green, Blue } Color deriving (Bits, Eq);" -- 2
  , ""                                                              -- 3
  , "function Color nextColor(Color c);"                           -- 4
  , "  case (c)"                                                   -- 5
  , "    Red:   return Green;"                                     -- 6
  , "    Green: return Blue;"                                      -- 7
  , "    Blue:  return Red;"                                       -- 8
  , "  endcase"                                                    -- 9
  , "endfunction"                                                  -- 10
  , "endpackage"                                                   -- 11
  ]

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

spec :: Spec
spec = do
  describe "BSV getDefinition" $ do

    describe "parsing" $ do
      it "parses simple BSV interface and module" $ do
        case parseAndBuild "BsvTest.bsv" bsvSimpleSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right _  -> pure ()

      it "parses BSV typedef and function" $ do
        case parseAndBuild "BsvTypes.bsv" bsvTypedefSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right _  -> pure ()

      it "parses BSV ternary expressions" $ do
        case parseAndBuild "BsvTernary.bsv" bsvTernarySource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right _  -> pure ()

      it "parses BSV enum typedef" $ do
        case parseAndBuild "BsvEnum.bsv" bsvEnumSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right _  -> pure ()

    describe "interface definitions" $ do
      it "finds interface definition when cursor is on interface name" $ do
        case parseAndBuild "BsvTest.bsv" bsvSimpleSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "interface IFoo;" — IFoo at col 10
            let result = getDefinition st bsvSimpleSource (pos 2 10)
            case result of
              Nothing  -> expectationFailure "Expected to find IFoo interface definition"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvSimpleSource loc `shouldBe` Just "IFoo"

      it "finds module definition when cursor is on module name" $ do
        case parseAndBuild "BsvTest.bsv" bsvSimpleSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "module mkFoo(IFoo);" — mkFoo at col 7
            let result = getDefinition st bsvSimpleSource (pos 7 7)
            case result of
              Nothing  -> expectationFailure "Expected to find mkFoo module definition"
              Just loc -> do
                locLine loc `shouldBe` 7
                getSymbolNameAt bsvSimpleSource loc `shouldBe` Just "mkFoo"

    describe "typedef definitions" $ do
      it "finds typedef definition when cursor is on the type name" $ do
        case parseAndBuild "BsvTypes.bsv" bsvTypedefSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "typedef UInt#(8) MyByte;" — MyByte at col 17
            let result = getDefinition st bsvTypedefSource (pos 2 17)
            case result of
              Nothing  -> expectationFailure "Expected to find MyByte typedef"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvTypedefSource loc `shouldBe` Just "MyByte"

      it "finds typedef when cursor is on type usage in function return type" $ do
        case parseAndBuild "BsvTypes.bsv" bsvTypedefSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "function MyByte increment(MyByte x);" — first MyByte at col 9
            let result = getDefinition st bsvTypedefSource (pos 4 9)
            case result of
              Nothing  -> expectationFailure "Expected to find MyByte typedef from usage"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvTypedefSource loc `shouldBe` Just "MyByte"

      it "finds typedef when cursor is on type usage in function parameter" $ do
        case parseAndBuild "BsvTypes.bsv" bsvTypedefSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "function MyByte increment(MyByte x);" — second MyByte at col 26
            let result = getDefinition st bsvTypedefSource (pos 4 26)
            case result of
              Nothing  -> expectationFailure "Expected to find MyByte typedef from parameter usage"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvTypedefSource loc `shouldBe` Just "MyByte"

    describe "function definitions" $ do
      it "finds function definition when cursor is on function name" $ do
        case parseAndBuild "BsvTypes.bsv" bsvTypedefSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "function MyByte increment(MyByte x);" — increment at col 16
            let result = getDefinition st bsvTypedefSource (pos 4 16)
            case result of
              Nothing  -> expectationFailure "Expected to find increment function"
              Just loc -> do
                locLine loc `shouldBe` 4
                getSymbolNameAt bsvTypedefSource loc `shouldBe` Just "increment"

    describe "ternary expression" $ do
      it "parses ternary and finds function definition" $ do
        case parseAndBuild "BsvTernary.bsv" bsvTernarySource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "function Bit#(2) chooseMxl(Bool is32);" — chooseMxl at col 17
            let result = getDefinition st bsvTernarySource (pos 2 17)
            case result of
              Nothing  -> expectationFailure "Expected to find chooseMxl function"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvTernarySource loc `shouldBe` Just "chooseMxl"

    describe "enum typedef" $ do
      it "finds enum type definition" $ do
        case parseAndBuild "BsvEnum.bsv" bsvEnumSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "typedef enum { Red, Green, Blue } Color ..."  — Color at col 34
            let result = getDefinition st bsvEnumSource (pos 2 34)
            case result of
              Nothing  -> expectationFailure "Expected to find Color typedef"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvEnumSource loc `shouldBe` Just "Color"

      it "finds enum constructor definition" $ do
        case parseAndBuild "BsvEnum.bsv" bsvEnumSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "typedef enum { Red, Green, Blue } ..." — Red at col 15
            let result = getDefinition st bsvEnumSource (pos 2 15)
            case result of
              Nothing  -> expectationFailure "Expected to find Red constructor"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvEnumSource loc `shouldBe` Just "Red"

      it "finds enum type when used in function return type" $ do
        case parseAndBuild "BsvEnum.bsv" bsvEnumSource of
          Left err -> expectationFailure $ "Parse failed: " ++ err
          Right st -> do
            -- "function Color nextColor(Color c);" — first Color at col 9
            let result = getDefinition st bsvEnumSource (pos 4 9)
            case result of
              Nothing  -> expectationFailure "Expected to find Color typedef from usage"
              Just loc -> do
                locLine loc `shouldBe` 2
                getSymbolNameAt bsvEnumSource loc `shouldBe` Just "Color"
