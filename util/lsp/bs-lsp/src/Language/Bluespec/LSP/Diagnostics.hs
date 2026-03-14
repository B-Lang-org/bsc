-- | Convert parse errors to LSP diagnostics.
module Language.Bluespec.LSP.Diagnostics
  ( makeDiagnostics
  , parseErrorToDiagnostic
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle(..), ErrorItem(..), PosState(..))
import qualified Text.Megaparsec as MP

import Language.LSP.Protocol.Types

import qualified Language.Bluespec.Parser as Parser
import Language.Bluespec.Position (SrcSpan(..), Pos(..))
import Language.Bluespec.Syntax (Package)
import qualified Language.Bluespec.Lexer as Lex

-- | Convert parse result to LSP diagnostics.
makeDiagnostics :: Either Parser.ParseError Package -> [Diagnostic]
makeDiagnostics (Right _) = []
makeDiagnostics (Left err) = parseErrorBundleToDiagnostics err

-- | Convert a parse error bundle to LSP diagnostics.
parseErrorBundleToDiagnostics :: Parser.ParseError -> [Diagnostic]
parseErrorBundleToDiagnostics ParseErrorBundle{..} =
  map (parseErrorToDiagnostic (pstateInput bundlePosState)) (NE.toList bundleErrors)

-- | Convert a single parse error to an LSP diagnostic.
parseErrorToDiagnostic :: Lex.TokenStream -> MP.ParseError Lex.TokenStream Void -> Diagnostic
parseErrorToDiagnostic posState err = Diagnostic
  { _range = errorRange
  , _severity = Just DiagnosticSeverity_Error
  , _code = Nothing
  , _codeDescription = Nothing
  , _source = Just "bluespec"
  , _message = errorMessage
  , _tags = Nothing
  , _relatedInformation = Nothing
  , _data_ = Nothing
  }
  where
    -- Get error position
    errorRange = case err of
      MP.TrivialError offset _ _ -> offsetToRange posState offset
      MP.FancyError offset _ -> offsetToRange posState offset

    -- Format error message
    errorMessage = formatError err

-- | Convert offset to LSP Range using token stream info.
offsetToRange :: Lex.TokenStream -> Int -> Range
offsetToRange ts offset = Range start end
  where
    tokens = Lex.unTokenStream ts
    -- Find token at offset
    (line, col) = case drop offset tokens of
      (tok:_) ->
        let spn = Lex.tokSpan tok
            pos = spanBegin spn
        in (posLine pos, posColumn pos)
      [] -> case reverse tokens of
        (tok:_) ->
          let spn = Lex.tokSpan tok
              pos = spanFinal spn
          in (posLine pos, posColumn pos)
        [] -> (1, 1)
    -- LSP positions are 0-indexed
    start = Position (fromIntegral (line - 1)) (fromIntegral (col - 1))
    end = Position (fromIntegral (line - 1)) (fromIntegral col)

-- | Format a parse error as a readable message.
formatError :: MP.ParseError Lex.TokenStream Void -> Text
formatError (MP.TrivialError _ unexpected expected) = T.unlines $
  filter (not . T.null)
  [ formatUnexpected unexpected
  , formatExpected expected
  ]
formatError (MP.FancyError _ errs) = T.unlines $
  map (T.pack . show) (Set.toList errs)

-- | Format unexpected item.
formatUnexpected :: Maybe (ErrorItem Lex.Token) -> Text
formatUnexpected Nothing = "Unexpected end of input"
formatUnexpected (Just (Tokens toks)) =
  "Unexpected " <> formatTokens (NE.toList toks)
formatUnexpected (Just (Label label)) =
  "Unexpected " <> T.pack (NE.toList label)
formatUnexpected (Just EndOfInput) =
  "Unexpected end of input"

-- | Format expected items.
formatExpected :: Set.Set (ErrorItem Lex.Token) -> Text
formatExpected items
  | Set.null items = ""
  | otherwise = "Expected: " <> T.intercalate ", " (map formatItem $ Set.toList items)

-- | Format a single error item.
formatItem :: ErrorItem Lex.Token -> Text
formatItem (Tokens toks) = formatTokens (NE.toList toks)
formatItem (Label label) = T.pack (NE.toList label)
formatItem EndOfInput = "end of input"

-- | Format tokens for display.
formatTokens :: [Lex.Token] -> Text
formatTokens [] = "<empty>"
formatTokens toks = T.intercalate " " $ map formatToken toks

-- | Format a single token for display.
formatToken :: Lex.Token -> Text
formatToken tok = case Lex.tokKind tok of
  Lex.TokVarId name -> "'" <> name <> "'"
  Lex.TokConId name -> "'" <> name <> "'"
  Lex.TokQVarId m n -> "'" <> m <> "." <> n <> "'"
  Lex.TokQConId m n -> "'" <> m <> "." <> n <> "'"
  Lex.TokVarSym sym -> "'" <> sym <> "'"
  Lex.TokConSym sym -> "'" <> sym <> "'"
  Lex.TokQVarSym m s -> "'" <> m <> "." <> s <> "'"
  Lex.TokQConSym m s -> "'" <> m <> "." <> s <> "'"
  Lex.TokInteger n _ -> T.pack (show n)
  Lex.TokFloat f -> T.pack (show f)
  Lex.TokChar c -> "'" <> T.singleton c <> "'"
  Lex.TokString s -> "\"" <> s <> "\""
  Lex.TokKeyword kw -> "'" <> T.pack (show kw) <> "'"
  Lex.TokPunct p -> "'" <> T.pack (show p) <> "'"
  Lex.TokVLBrace -> "'{'"
  Lex.TokVRBrace -> "'}'"
  Lex.TokVSemi -> "';'"
  Lex.TokEOF -> "end of file"
  Lex.TokPragmaStart -> "'{-#'"
  Lex.TokPragmaEnd -> "'#-}'"
  Lex.TokPragmaContent _ -> "pragma content"
