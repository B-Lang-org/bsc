{-# LANGUAGE TypeFamilies #-}

-- | Lexer for Bluespec Classic.
module Language.Bluespec.Lexer
  ( -- * Token types
    Token (..)
  , TokenKind (..)
  , Keyword (..)
  , Punctuation (..)
  , IntFormat' (..)

    -- * Lexer
  , lexBluespec
  , tokenize
  , keywordText

    -- * Token stream for parser
  , TokenStream (..)
  , scanTokens
  ) where

import Control.Monad (void, when)
import Data.Char (isAlpha, isAlphaNum, isDigit, isHexDigit, isOctDigit, isSpace)
import Data.List (foldl')
import Data.List.NonEmpty (toList)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec hiding (Token, Tokens, token)
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Language.Bluespec.Position hiding (mkPos)
import qualified Language.Bluespec.Position as Pos

--------------------------------------------------------------------------------
-- Token Types
--------------------------------------------------------------------------------

-- | A token with source position.
data Token = Token
  { tokSpan :: !SrcSpan
  , tokKind :: !TokenKind
  }
  deriving stock (Eq, Show)

-- | Ord instance for Token (required by megaparsec Stream).
instance Ord Token where
  compare t1 t2 = compare (tokSpan t1) (tokSpan t2)

-- | Token kinds.
data TokenKind
  -- Identifiers
  = TokVarId !Text           -- ^ Lowercase identifier
  | TokConId !Text           -- ^ Uppercase identifier
  | TokQVarId !Text !Text    -- ^ Qualified lowercase identifier
  | TokQConId !Text !Text    -- ^ Qualified uppercase identifier

  -- Operators
  | TokVarSym !Text          -- ^ Symbolic operator (e.g., +, -, *, etc.)
  | TokConSym !Text          -- ^ Constructor operator (e.g., :+:)
  | TokQVarSym !Text !Text   -- ^ Qualified symbolic operator
  | TokQConSym !Text !Text   -- ^ Qualified constructor operator

  -- Literals
  | TokInteger !Integer !(Maybe (Int, IntFormat'))  -- ^ Integer literal
  | TokFloat !Double                                -- ^ Float literal
  | TokChar !Char                                   -- ^ Character literal
  | TokString !Text                                 -- ^ String literal

  -- Keywords
  | TokKeyword !Keyword

  -- Punctuation
  | TokPunct !Punctuation

  -- Layout tokens (inserted by layout processor)
  | TokVLBrace              -- ^ Virtual left brace
  | TokVRBrace              -- ^ Virtual right brace
  | TokVSemi                -- ^ Virtual semicolon

  -- Special
  | TokEOF                  -- ^ End of file
  | TokPragmaStart          -- ^ {-#
  | TokPragmaEnd            -- ^ #-}
  | TokPragmaContent !Text  -- ^ Content inside pragma
  deriving stock (Eq, Show)

-- | Integer format (duplicate to avoid import cycle).
data IntFormat'
  = IntDec'
  | IntHex'
  | IntBin'
  | IntOct'
  deriving stock (Eq, Show)

-- | Keywords in Bluespec.
data Keyword
  = KwAction
  | KwActionValue
  | KwCase
  | KwClass
  | KwCoherent
  | KwData
  | KwDefault
  | KwDeriving
  | KwDo
  | KwElse
  | KwForeign
  | KwIf
  | KwImport
  | KwIn
  | KwIncoherent
  | KwInfix
  | KwInfixL
  | KwInfixR
  | KwInstance
  | KwInterface
  | KwLet
  | KwLetSeq
  | KwModule
  | KwOf
  | KwPackage
  | KwPrimitive
  | KwQualified
  | KwRules
  | KwStruct
  | KwThen
  | KwType
  | KwValueOf
  | KwStringOf
  | KwVerilog
  | KwSynthesize
  | KwWhen
  | KwWhere
  -- BSV-specific keywords
  | KwBegin           -- ^ begin
  | KwBreak           -- ^ break
  | KwContinue        -- ^ continue
  | KwEnd             -- ^ end
  | KwEndAction       -- ^ endaction
  | KwEndActionValue  -- ^ endactionvalue
  | KwEndCase         -- ^ endcase
  | KwEndFunction     -- ^ endfunction
  | KwEndInstance     -- ^ endinstance
  | KwEndInterface    -- ^ endinterface
  | KwEndMethod       -- ^ endmethod
  | KwEndModule       -- ^ endmodule
  | KwEndPackage      -- ^ endpackage
  | KwEndPar          -- ^ endpar
  | KwEndRule         -- ^ endrule
  | KwEndRules        -- ^ endrules
  | KwEndSeq          -- ^ endseq
  | KwEndTypeclass    -- ^ endtypeclass
  | KwEnum            -- ^ enum
  | KwExport          -- ^ export (BSV)
  | KwFor             -- ^ for
  | KwFunction        -- ^ function
  | KwMatches         -- ^ matches
  | KwMethod          -- ^ method (BSV method opening)
  | KwNumeric         -- ^ numeric
  | KwParameter       -- ^ parameter
  | KwProvisos        -- ^ provisos
  | KwRepeat          -- ^ repeat
  | KwReturn          -- ^ return
  | KwRule            -- ^ rule (BSV rule opening, different from Classic 'rules')
  | KwTagged          -- ^ tagged
  | KwTypedef         -- ^ typedef
  | KwUnion           -- ^ union
  | KwVoid            -- ^ void
  | KwWhile           -- ^ while
  deriving stock (Eq, Show, Bounded, Enum)

-- | Punctuation tokens.
data Punctuation
  = PunctLParen       -- ^ (
  | PunctRParen       -- ^ )
  | PunctLBracket     -- ^ [
  | PunctRBracket     -- ^ ]
  | PunctLBrace       -- ^ {
  | PunctRBrace       -- ^ }
  | PunctComma        -- ^ ,
  | PunctSemi         -- ^ ;
  | PunctBacktick     -- ^ `
  | PunctColon        -- ^ :
  | PunctDColon       -- ^ ::
  | PunctDot          -- ^ .
  | PunctDDot         -- ^ ..
  | PunctEqual        -- ^ =
  | PunctBackslash    -- ^ \
  | PunctAt           -- ^ @
  | PunctUnderscore   -- ^ _
  | PunctArrow        -- ^ ->
  | PunctLArrow       -- ^ <-
  | PunctFatArrow     -- ^ =>
  | PunctRuleArrow    -- ^ ==>
  | PunctColonEq      -- ^ :=
  | PunctTilde        -- ^ ~
  | PunctHash         -- ^ #
  | PunctTick         -- ^ ' (BSV type cast)
  deriving stock (Eq, Show, Bounded, Enum)

--------------------------------------------------------------------------------
-- Keyword and Punctuation Maps
--------------------------------------------------------------------------------

keywords :: [(Text, Keyword)]
keywords =
  [ ("action", KwAction)
  , ("actionvalue", KwActionValue)
  , ("case", KwCase)
  , ("class", KwClass)
  , ("coherent", KwCoherent)
  , ("data", KwData)
  , ("default", KwDefault)
  , ("deriving", KwDeriving)
  , ("do", KwDo)
  , ("else", KwElse)
  , ("foreign", KwForeign)
  , ("if", KwIf)
  , ("import", KwImport)
  , ("in", KwIn)
  , ("incoherent", KwIncoherent)
  , ("infix", KwInfix)
  , ("infixl", KwInfixL)
  , ("infixr", KwInfixR)
  , ("instance", KwInstance)
  , ("interface", KwInterface)
  , ("let", KwLet)
  , ("letseq", KwLetSeq)
  , ("module", KwModule)
  , ("of", KwOf)
  , ("package", KwPackage)
  , ("primitive", KwPrimitive)
  , ("qualified", KwQualified)
  , ("rules", KwRules)
  , ("struct", KwStruct)
  , ("then", KwThen)
  , ("type", KwType)
  , ("valueOf", KwValueOf)
  , ("valueof", KwValueOf)   -- BSV lowercase alias
  , ("stringOf", KwStringOf)
  , ("verilog", KwVerilog)
  , ("synthesize", KwSynthesize)
  , ("when", KwWhen)
  , ("where", KwWhere)
  -- BSV-specific keywords
  , ("begin", KwBegin)
  , ("break", KwBreak)
  , ("continue", KwContinue)
  , ("end", KwEnd)
  , ("endaction", KwEndAction)
  , ("endactionvalue", KwEndActionValue)
  , ("endcase", KwEndCase)
  , ("endfunction", KwEndFunction)
  , ("endinstance", KwEndInstance)
  , ("endinterface", KwEndInterface)
  , ("endmethod", KwEndMethod)
  , ("endmodule", KwEndModule)
  , ("endpackage", KwEndPackage)
  , ("endpar", KwEndPar)
  , ("endrule", KwEndRule)
  , ("endrules", KwEndRules)
  , ("endseq", KwEndSeq)
  , ("endtypeclass", KwEndTypeclass)
  , ("enum", KwEnum)
  , ("export", KwExport)
  , ("for", KwFor)
  , ("function", KwFunction)
  , ("matches", KwMatches)
  , ("method", KwMethod)
  , ("numeric", KwNumeric)
  , ("parameter", KwParameter)
  , ("provisos", KwProvisos)
  , ("repeat", KwRepeat)
  , ("return", KwReturn)
  , ("rule", KwRule)
  , ("tagged", KwTagged)
  , ("typedef", KwTypedef)
  , ("union", KwUnion)
  , ("void", KwVoid)
  , ("while", KwWhile)
  ]

keywordMap :: Text -> Maybe Keyword
keywordMap t = lookup t keywords

-- | The source text for a keyword.
keywordText :: Keyword -> Text
keywordText kw = case filter ((== kw) . snd) keywords of
  ((t, _):_) -> t
  []          -> error "keywordText: unknown keyword"

--------------------------------------------------------------------------------
-- Lexer Type
--------------------------------------------------------------------------------

type Lexer = Parsec Void Text

--------------------------------------------------------------------------------
-- Space and Comments
--------------------------------------------------------------------------------

-- | Skip whitespace and comments.
-- Handles both Bluespec Classic ({- -}, --) and BSV (/* */, //) comment styles.
sc :: Lexer ()
sc = L.space space1 lineComment blockComment
  where
    lineComment  = L.skipLineComment "--" <|> L.skipLineComment "//"
    -- Block comment: either BSV C-style (/* */) or Classic Haskell-style ({- -})
    blockComment = cStyleBlockComment <|> haskellBlockComment
    cStyleBlockComment = do
      void $ try $ string "/*"
      void $ manyTill anySingle (string "*/")
    -- Block comment that doesn't match pragmas ({-#)
    haskellBlockComment = do
      void $ try $ string "{-" <* notFollowedBy (char '#')
      skipBlockCommentNested 1
    skipBlockCommentNested :: Int -> Lexer ()
    skipBlockCommentNested 0 = pure ()
    skipBlockCommentNested n = do
      _ <- takeWhileP Nothing (\c -> c /= '{' && c /= '-' && c /= '#')
      choice
        [ try (string "#-}") >> skipBlockCommentNested (n - 1)  -- pragma end closes nesting
        , try (string "-}") >> skipBlockCommentNested (n - 1)   -- block comment end
        , try (string "{-#") >> skipBlockCommentNested (n + 1)  -- pragma start opens nesting
        , try (string "{-") >> skipBlockCommentNested (n + 1)   -- nested block comment
        , anySingle >> skipBlockCommentNested n
        ]

-- | Skip whitespace but not newlines.
scNoNewline :: Lexer ()
scNoNewline = void $ takeWhileP Nothing (\c -> isSpace c && c /= '\n' && c /= '\r')

--------------------------------------------------------------------------------
-- Lexer Primitives
--------------------------------------------------------------------------------

-- | Get current position.
getPosition :: Lexer Pos.Pos
getPosition = do
  sp <- getSourcePos
  pure $ Pos.Pos (unPos $ sourceLine sp) (unPos $ sourceColumn sp)

-- | Lex with position tracking.
withSpan :: Text -> Lexer TokenKind -> Lexer Token
withSpan file p = do
  start <- getPosition
  kind <- p
  end <- getPosition
  pure $ Token (SrcSpan file start end) kind

--------------------------------------------------------------------------------
-- Identifier Lexers
--------------------------------------------------------------------------------

-- | Check if character can start an identifier.
isIdentStart :: Char -> Bool
isIdentStart c = isAlpha c || c == '_'

-- | Check if character can continue an identifier.
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

-- | Lex a lowercase identifier or keyword.
varIdOrKeyword :: Lexer TokenKind
varIdOrKeyword = do
  c <- satisfy (\x -> isIdentStart x && (x < 'A' || x > 'Z'))
  rest <- takeWhileP Nothing isIdentChar
  let ident = T.cons c rest
  pure $ case keywordMap ident of
    Just kw -> TokKeyword kw
    Nothing -> TokVarId ident

-- | Lex an uppercase identifier.
conId :: Lexer TokenKind
conId = do
  c <- satisfy (\x -> x >= 'A' && x <= 'Z')
  rest <- takeWhileP Nothing isIdentChar
  let ident = T.cons c rest
  -- Check for qualified name (use lookAhead to check without consuming)
  mDot <- optional (try (lookAhead (char '.' *> satisfy (\x -> isIdentStart x || isOpChar x))))
  case mDot of
    Just _ -> do
      void $ char '.'  -- Now consume the dot
      nextCh <- lookAhead anySingle
      if isIdentStart nextCh
        then do
          qIdent <- takeWhile1P Nothing isIdentChar
          pure $ if isUpper (T.head qIdent)
            then TokQConId ident qIdent
            else TokQVarId ident qIdent
        else do
          -- qualified operator: Prelude.+ etc.
          op <- takeWhile1P Nothing isOpChar
          pure $ TokQVarSym ident op
    Nothing -> pure $ TokConId ident
  where
    isUpper x = x >= 'A' && x <= 'Z'

--------------------------------------------------------------------------------
-- Operator Lexers
--------------------------------------------------------------------------------

-- | Characters that can appear in operators.
isOpChar :: Char -> Bool
isOpChar c = c `elem` ("!#$%&*+./<=>?@\\^|-~:" :: String) || c == '\x2218'  -- ∘
          || c == '\x00BB'  -- »

-- | Reserved operators that are punctuation.
reservedOps :: [(Text, Punctuation)]
reservedOps =
  [ ("::", PunctDColon)
  , (":", PunctColon)
  , ("..", PunctDDot)
  , (".", PunctDot)
  , ("==>", PunctRuleArrow)
  , ("=>", PunctFatArrow)
  , ("=", PunctEqual)
  , (":=", PunctColonEq)
  , ("->", PunctArrow)
  , ("<-", PunctLArrow)
  , ("@", PunctAt)
  , ("\\", PunctBackslash)
  , ("~", PunctTilde)
  , ("#", PunctHash)
  ]

-- | Lex an operator.
operator :: Lexer TokenKind
operator = do
  op <- takeWhile1P (Just "operator") isOpChar
  -- Check for reserved operators
  case lookup op reservedOps of
    Just p -> pure $ TokPunct p
    Nothing
      | ":" `T.isPrefixOf` op -> pure $ TokConSym op
      | otherwise -> pure $ TokVarSym op

--------------------------------------------------------------------------------
-- Numeric Lexers
--------------------------------------------------------------------------------

-- | Lex a numeric literal.
numericLit :: Lexer TokenKind
numericLit = sized <|> tickPrefixed <|> unsized
  where
    -- Sized bit literals: 8'hFF, 4'b1010
    sized = try $ do
      width <- L.decimal
      void $ char '\''
      (val, fmt) <- sizedFormat
      pure $ TokInteger val (Just (width, fmt))

    -- BSV tick-prefixed literals: 'hFF, 'b1010, 'o77, 'd42
    tickPrefixed = try $ do
      void $ char '\''
      choice
        [ (char 'h' <|> char 'H') *> (TokInteger <$> hexNum <*> pure (Just (0, IntHex')))
        , (char 'b' <|> char 'B') *> (TokInteger <$> binNum <*> pure (Just (0, IntBin')))
        , (char 'o' <|> char 'O') *> (TokInteger <$> octNum <*> pure (Just (0, IntOct')))
        , (char 'd' <|> char 'D') *> (TokInteger <$> L.decimal <*> pure (Just (0, IntDec')))
        ]

    sizedFormat =
          (char 'h' *> ((,IntHex') <$> hexNum))
      <|> (char 'd' *> ((,IntDec') <$> L.decimal))
      <|> (char 'b' *> ((,IntBin') <$> binNum))
      <|> (char 'o' *> ((,IntOct') <$> octNum))

    -- Unsized literals: 0xFF, 0b1010, 123, 1.5
    unsized = do
      prefix <- optional $ try $ string "0" *> oneOf ("xXbBoO" :: String)
      case prefix of
        Just 'x' -> TokInteger <$> hexNum <*> pure (Just (0, IntHex'))
        Just 'X' -> TokInteger <$> hexNum <*> pure (Just (0, IntHex'))
        Just 'b' -> TokInteger <$> binNum <*> pure (Just (0, IntBin'))
        Just 'B' -> TokInteger <$> binNum <*> pure (Just (0, IntBin'))
        Just 'o' -> TokInteger <$> octNum <*> pure (Just (0, IntOct'))
        Just 'O' -> TokInteger <$> octNum <*> pure (Just (0, IntOct'))
        Just _   -> error "impossible"
        Nothing  -> decOrFloat

    decOrFloat = do
      int <- L.decimal
      mFrac <- optional $ try $ do
        void $ char '.'
        frac <- takeWhile1P Nothing isDigit
        pure frac
      case mFrac of
        Just frac -> do
          mExp <- optional $ try $ do
            void $ oneOf ("eE" :: String)
            sign <- option "" (T.singleton <$> oneOf ("+-" :: String))
            exp' <- takeWhile1P Nothing isDigit
            pure (sign <> exp')
          -- Haskell's 'read :: Double' doesn't accept 'e+N'; normalise to 'eN' or 'e-N'.
          let normExp = fmap (\e -> if T.isPrefixOf "+" e then T.drop 1 e else e) mExp
          let floatStr = T.pack (show int) <> "." <> frac <> maybe "" ("e" <>) normExp
          pure $ TokFloat (read $ T.unpack floatStr)
        Nothing -> do
          mExp <- optional $ try $ do
            void $ oneOf ("eE" :: String)
            sign <- option "" (T.singleton <$> oneOf ("+-" :: String))
            exp' <- takeWhile1P Nothing isDigit
            pure (sign <> exp')
          case mExp of
            Just exp' -> do
              let normExp = if T.isPrefixOf "+" exp' then T.drop 1 exp' else exp'
              let floatStr = T.pack (show int) <> "e" <> normExp
              pure $ TokFloat (read $ T.unpack floatStr)
            Nothing -> pure $ TokInteger int Nothing

    hexNum = foldl' (\a d -> a * 16 + fromIntegral (hexDigitVal d)) 0 . T.unpack <$>
             takeWhile1P (Just "hex digit") isHexDigit

    binNum = foldl' (\a d -> a * 2 + if d == '1' then 1 else 0) 0 . T.unpack <$>
             takeWhile1P (Just "binary digit") (\c -> c == '0' || c == '1')

    octNum = foldl' (\a d -> a * 8 + fromIntegral (octDigitVal d)) 0 . T.unpack <$>
             takeWhile1P (Just "octal digit") isOctDigit

    hexDigitVal :: Char -> Int
    hexDigitVal c
      | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
      | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
      | c >= 'A' && c <= 'F' = fromEnum c - fromEnum 'A' + 10
      | otherwise = 0

    octDigitVal :: Char -> Int
    octDigitVal c = fromEnum c - fromEnum '0'

--------------------------------------------------------------------------------
-- Character and String Lexers
--------------------------------------------------------------------------------

-- | Lex a character literal.
charLit :: Lexer TokenKind
charLit = do
  void $ char '\''
  c <- charContent
  void $ char '\''
  pure $ TokChar c

-- | Lex a string literal.
stringLit :: Lexer TokenKind
stringLit = do
  void $ char '"'
  cs <- many stringContent
  void $ char '"'
  pure $ TokString (T.pack cs)

-- | Parse a single character in a char literal.
charContent :: Lexer Char
charContent = escapeChar <|> satisfy (\c -> c /= '\'' && c /= '\\')

-- | Parse a single character in a string literal.
stringContent :: Lexer Char
stringContent = escapeChar <|> satisfy (\c -> c /= '"' && c /= '\\')

-- | Parse an escape sequence.
escapeChar :: Lexer Char
escapeChar = do
  void $ char '\\'
  c <- anySingle
  case c of
    'n'  -> pure '\n'
    't'  -> pure '\t'
    'r'  -> pure '\r'
    '\\' -> pure '\\'
    '\'' -> pure '\''
    '"'  -> pure '"'
    '0'  -> pure '\0'
    'x'  -> do
      d1 <- satisfy isHexDigit
      d2 <- satisfy isHexDigit
      pure $ toEnum (hexVal d1 * 16 + hexVal d2)
    _    -> pure c
  where
    hexVal c
      | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
      | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
      | c >= 'A' && c <= 'F' = fromEnum c - fromEnum 'A' + 10
      | otherwise = 0

--------------------------------------------------------------------------------
-- Punctuation Lexer
--------------------------------------------------------------------------------

-- | Lex single-character punctuation.
punctuation :: Lexer TokenKind
punctuation = choice
  [ TokPunct PunctLParen     <$ char '('
  , TokPunct PunctRParen     <$ char ')'
  , TokPunct PunctLBracket   <$ char '['
  , TokPunct PunctRBracket   <$ char ']'
  , TokPunct PunctLBrace     <$ char '{'
  , TokPunct PunctRBrace     <$ char '}'
  , TokPunct PunctComma      <$ char ','
  , TokPunct PunctSemi       <$ char ';'
  , TokPunct PunctBacktick   <$ char '`'
  , TokPunct PunctUnderscore <$ char '_' <* notFollowedBy (satisfy isIdentChar)
  ]

--------------------------------------------------------------------------------
-- Pragma Lexer
--------------------------------------------------------------------------------

-- | Lex a pragma.
pragma :: Lexer TokenKind
pragma = do
  void $ string "{-#"
  pure TokPragmaStart

pragmaEnd :: Lexer TokenKind
pragmaEnd = do
  void $ string "#-}"
  pure TokPragmaEnd

--------------------------------------------------------------------------------
-- Primitive Operations ($display, etc.)
--------------------------------------------------------------------------------

-- | Lex a primitive operation starting with $.
-- Handles identifiers like $display, $test$plusargs (with multiple $ parts).
primOp :: Lexer TokenKind
primOp = do
  void $ char '$'
  -- Parse the first part
  first <- takeWhile1P Nothing isIdentChar
  -- Parse any additional $part sections (e.g., $test$plusargs)
  rest <- many $ try $ do
    void $ char '$'
    takeWhile1P Nothing isIdentChar
  let name = "$" <> first <> T.concat (map ("$" <>) rest)
  pure $ TokVarId name

--------------------------------------------------------------------------------
-- Main Token Lexer
--------------------------------------------------------------------------------

-- | Lex a single token.
token' :: Text -> Lexer Token
token' file = withSpan file $ choice
  [ try pragma
  , try pragmaEnd
  , try primOp
  , try numericLit   -- includes 'h... 'b... tick-prefixed BSV literals
  , try charLit      -- 'c' character literals
  , TokPunct PunctTick <$ char '\''  -- bare ' (BSV type cast)
  , stringLit
  , conId
  , varIdOrKeyword
  , operator
  , punctuation
  ]

-- | Lex all tokens from input.
lexBluespec :: Text -> Text -> Either (ParseErrorBundle Text Void) [Token]
lexBluespec file input = parse (tokens file) (T.unpack file) input
  where
    tokens f = do
      sc
      ts <- many (token' f <* sc)
      eof
      pos <- getPosition
      let eofTok = Token (SrcSpan f pos pos) TokEOF
      pure (ts ++ [eofTok])

-- | Tokenize input, returning error message on failure.
tokenize :: Text -> Text -> Either String [Token]
tokenize file input = case lexBluespec file input of
  Left err -> Left (errorBundlePretty err)
  Right ts -> Right ts

--------------------------------------------------------------------------------
-- Token Stream for Megaparsec
--------------------------------------------------------------------------------

-- | A token stream for use with megaparsec.
newtype TokenStream = TokenStream { unTokenStream :: [Token] }
  deriving stock (Eq, Show)

instance Stream TokenStream where
  type Token TokenStream = Token
  type Tokens TokenStream = [Token]

  tokenToChunk _ = (:[])
  tokensToChunk _ = id
  chunkToTokens _ = id
  chunkLength _ = length
  chunkEmpty _ = null

  take1_ (TokenStream []) = Nothing
  take1_ (TokenStream (t:ts)) = Just (t, TokenStream ts)

  takeN_ n (TokenStream ts)
    | n <= 0 = Just ([], TokenStream ts)
    | null ts = Nothing
    | otherwise = Just (take n ts, TokenStream (drop n ts))

  takeWhile_ f (TokenStream ts) =
    let (h, t) = span f ts
    in (h, TokenStream t)

instance VisualStream TokenStream where
  showTokens _ = unwords . map showToken . toList
    where
      showToken tok = show (tokKind tok)

instance TraversableStream TokenStream where
  reachOffset o pst =
    let (pre, post) = splitAt (o - pstateOffset pst) (unTokenStream $ pstateInput pst)
        newPos = case post of
          (t:_) -> let sp = tokSpan t
                       p = spanBegin sp
                   in SourcePos (T.unpack $ spanFile sp) (mkPos $ Pos.posLine p) (mkPos $ Pos.posColumn p)
          [] -> pstateSourcePos pst
    in ( Just (T.unpack $ T.intercalate " " $ map (T.pack . show . tokKind) pre)
       , pst { pstateInput = TokenStream post
             , pstateOffset = o
             , pstateSourcePos = newPos
             }
       )

-- | Create a token stream for parsing.
scanTokens :: Text -> Text -> Either String TokenStream
scanTokens file input = TokenStream <$> tokenize file input
