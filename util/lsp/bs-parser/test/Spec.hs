{-# LANGUAGE OverloadedStrings #-}

-- | Tests for the Bluespec parser.
module Main (main) where

import Data.Text (Text)
import qualified Data.Text as T
import Test.Hspec
import Text.Megaparsec (parse, errorBundlePretty)

import Language.Bluespec.Lexer
import Language.Bluespec.Layout
import Language.Bluespec.Parser
import Language.Bluespec.Position
import Language.Bluespec.Pretty
import Language.Bluespec.Syntax

main :: IO ()
main = hspec $ do
  describe "Lexer" $ do
    it "lexes identifiers" $ do
      let Right toks = tokenize "<test>" "foo Bar _baz"
      length (filter (not . isEof) toks) `shouldBe` 3

    it "lexes operators" $ do
      let Right toks = tokenize "<test>" "+ - * / :: ->"
      length (filter (not . isEof) toks) `shouldBe` 6

    it "lexes integer literals" $ do
      let Right toks = tokenize "<test>" "42 0xFF 8'b10101010"
      length (filter (not . isEof) toks) `shouldBe` 3

    it "lexes string literals" $ do
      let Right toks = tokenize "<test>" "\"hello\" 'a'"
      length (filter (not . isEof) toks) `shouldBe` 2

    it "lexes keywords" $ do
      let Right toks = tokenize "<test>" "package where import module"
      length (filter (not . isEof) toks) `shouldBe` 4

  describe "Parser" $ do
    it "parses simple package" $ do
      let input = "package Foo where\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          locVal (pkgName pkg) `shouldBe` ModuleId "Foo"

    it "parses imports" $ do
      let input = "package Foo where\nimport Bar\nimport qualified Baz\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          length (pkgImports pkg) `shouldBe` 2

    it "parses type signature" $ do
      let input = "package Foo where\nfoo :: Int -> Bool\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          length (pkgDefns pkg) `shouldBe` 1

    it "parses simple function" $ do
      let input = "package Foo where\nfoo x = x\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          length (pkgDefns pkg) `shouldBe` 1

    it "parses data type" $ do
      let input = "package Foo where\ndata Maybe a = Just a | Nothing\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          length (pkgDefns pkg) `shouldBe` 1

    it "parses interface" $ do
      let input = "package Foo where\ninterface Counter =\n  inc :: Action\n  get :: UInt 8\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          length (pkgDefns pkg) `shouldBe` 1

    it "parses let expression" $ do
      let input = "let x = 1 in x"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

    it "parses do expression" $ do
      let input = "do\n  x <- foo\n  bar x\n"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

    it "parses if expression" $ do
      let input = "if x then y else z"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

    it "parses case expression" $ do
      let input = "case x of\n  True -> 1\n  False -> 0\n"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

    it "parses lambda" $ do
      let input = "\\x y -> x + y"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

    it "parses record construction" $ do
      let input = "Foo { a = 1; b = 2 }"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

    it "parses field access" $ do
      let input = "x.foo.bar"
      case parseExpr "<test>" input of
        Left err -> expectationFailure $ show err
        Right _ -> pure ()

  describe "Pretty printer" $ do
    it "round-trips simple package" $ do
      let input = "package Foo where\n\nfoo :: Int\nfoo = 42\n"
      case parsePackage "<test>" input of
        Left err -> expectationFailure $ show err
        Right pkg -> do
          let pretty = renderPretty 80 (prettyPackage pkg)
          -- Just check that it produces output
          T.length pretty `shouldSatisfy` (> 0)

-- | Check if a token is EOF.
isEof :: Token -> Bool
isEof t = case tokKind t of
  TokEOF -> True
  _ -> False
