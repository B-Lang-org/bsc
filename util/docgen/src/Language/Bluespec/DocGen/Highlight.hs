-- | Syntax highlighting for Bluespec code blocks.
module Language.Bluespec.DocGen.Highlight
  ( highlightBluespec
  , highlightBSV
  , highlightAuto
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.Lexer
  ( Token (..), TokenKind (..), TokenStream (..), scanTokens
  , Keyword (..), Punctuation (..) )

import Language.Bluespec.DocGen.DocAST (Language (..))

highlightAuto :: Language -> Text -> Html
highlightAuto LangBSV      = highlightBSV
highlightAuto LangBluespec = highlightBluespec
highlightAuto _            = highlightPlain

highlightBluespec :: Text -> Html
highlightBluespec = highlightWith "bs"

highlightBSV :: Text -> Html
highlightBSV = highlightWith "bsv"

highlightPlain :: Text -> Html
highlightPlain src = H.pre $ H.toHtml src

highlightWith :: H.AttributeValue -> Text -> Html
highlightWith langClass src =
  H.pre ! A.class_ langClass $
    case scanTokens "<code>" src of
      Left _  -> H.toHtml src
      Right (TokenStream toks) ->
        mapM_ renderTok (filter notEOF toks)
  where
    notEOF tok = case tokKind tok of { TokEOF -> False; _ -> True }

renderTok :: Token -> Html
renderTok tok =
  let (cls, txt) = classify (tokKind tok)
  in case cls of
       Nothing -> H.toHtml txt
       Just c  -> H.span ! A.class_ c $ H.toHtml txt

classify :: TokenKind -> (Maybe H.AttributeValue, Text)
classify = \case
  TokVarId  t        -> (Just "id",  t)
  TokConId  t        -> (Just "ty",  t)
  TokQVarId _ t      -> (Just "id",  t)
  TokQConId _ t      -> (Just "ty",  t)
  TokVarSym t        -> (Just "op",  t)
  TokConSym t        -> (Just "op",  t)
  TokQVarSym _ t     -> (Just "op",  t)
  TokQConSym _ t     -> (Just "op",  t)
  TokString t        -> (Just "st",  "\"" <> t <> "\"")
  TokKeyword kw      -> (Just "kw",  kwText kw)
  TokPunct p         -> (Nothing,    pText p)
  TokVLBrace         -> (Nothing,    "{")
  TokVRBrace         -> (Nothing,    "}")
  TokVSemi           -> (Nothing,    ";")
  TokEOF             -> (Nothing,    "")
  TokPragmaStart     -> (Just "cm",  "{-#")
  TokPragmaEnd       -> (Just "cm",  "#-}")
  TokPragmaContent t -> (Just "cm",  t)
  -- Literals: source text not stored in token; use a generic label
  TokInteger _ _     -> (Just "lit", "0")
  TokFloat _         -> (Just "lit", "0.0")
  TokChar _          -> (Just "lit", "'?'")

-- Extract keyword source text from the constructor name.
-- KwFooBar -> "foobar", KwFoo -> "foo"
kwText :: Keyword -> Text
kwText kw = T.toLower $ T.pack $ stripKw $ show kw
  where
    stripKw ('K':'w':rest) = camelToKebab rest
    stripKw s              = s
    -- CamelCase -> lowercase (no separators for Bluespec keywords)
    camelToKebab = map toLowerC
    toLowerC c | c >= 'A' && c <= 'Z' = toEnum (fromEnum c + 32)
               | otherwise             = c

pText :: Punctuation -> Text
pText = \case
  PunctLParen     -> "("
  PunctRParen     -> ")"
  PunctLBracket   -> "["
  PunctRBracket   -> "]"
  PunctLBrace     -> "{"
  PunctRBrace     -> "}"
  PunctComma      -> ","
  PunctSemi       -> ";"
  PunctBacktick   -> "`"
  PunctColon      -> ":"
  PunctDColon     -> "::"
  PunctDot        -> "."
  PunctDDot       -> ".."
  PunctEqual      -> "="
  PunctBackslash  -> "\\"
  PunctAt         -> "@"
  PunctUnderscore -> "_"
  PunctArrow      -> "->"
  PunctLArrow     -> "<-"
  PunctFatArrow   -> "=>"
  PunctRuleArrow  -> "==>"
  PunctColonEq    -> ":="
  PunctTilde      -> "~"
  PunctHash       -> "#"
  PunctTick       -> "'"
