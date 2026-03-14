-- | Layout rule processor for Bluespec Classic.
--
-- This module implements the Haskell 2010 layout algorithm, which inserts
-- virtual braces and semicolons based on indentation.
module Language.Bluespec.Layout
  ( processLayout
  , isLayoutKeyword
  ) where

import Language.Bluespec.Lexer
import Language.Bluespec.Position

-- | Layout context: either explicit (0) or implicit (column number).
type LayoutContext = [Int]

-- | Keywords that always trigger a layout block.
isLayoutKeyword :: TokenKind -> Bool
isLayoutKeyword = \case
  TokKeyword KwWhere       -> True
  TokKeyword KwLet         -> True
  TokKeyword KwLetSeq      -> True
  TokKeyword KwDo          -> True
  TokKeyword KwAction      -> True
  TokKeyword KwActionValue -> True
  TokKeyword KwOf          -> True
  TokKeyword KwRules       -> True
  -- Note: KwModule is handled as a contextual layout keyword
  -- because 'module verilog ...' uses explicit braces
  _ -> False

-- | Keywords that are continuations of expressions and should NOT have
-- a virtual semicolon inserted before them, even at the same indentation.
-- This implements the "parse-error" rule from Haskell 2010 Section 10.3:
-- these keywords can never start a new statement, so inserting a semicolon
-- before them would always cause a parse error.
isContinuationKeyword :: TokenKind -> Bool
isContinuationKeyword = \case
  TokKeyword KwElse -> True   -- continues if-then-else
  TokKeyword KwThen -> True   -- continues if expression
  TokKeyword KwIn   -> True   -- continues let/letseq expression
  TokKeyword KwOf   -> True   -- continues case expression (but also triggers layout)
  _ -> False

-- | Keywords that only trigger layout when NOT followed by a specific keyword.
-- These are keywords that can appear both as definition headers (followed by
-- a constructor name) and as expressions (followed by field bindings).
-- Note: interface/struct are NOT here because interface expressions need layout
-- even when followed by a constructor name (the body follows the name).
-- Note: instance is NOT here because it only triggers layout via 'where'.
-- Note: class is NOT here because it only triggers layout via 'where'.
isContextualLayoutKeyword :: TokenKind -> Bool
isContextualLayoutKeyword = \case
  _ -> False

-- | Check if 'module' should trigger layout.
-- 'module' triggers layout unless followed by 'verilog' (for 'module verilog' syntax).
isModuleLayoutKeyword :: TokenKind -> Bool
isModuleLayoutKeyword = \case
  TokKeyword KwModule -> True
  _ -> False

-- | Check if token is 'verilog' keyword.
isVerilogKeyword :: TokenKind -> Bool
isVerilogKeyword = \case
  TokKeyword KwVerilog -> True
  _ -> False

-- | Keywords that trigger layout after ConId (for expressions with named bodies).
-- interface Foo <body>  -- expression, needs layout after Foo
-- struct Foo <body>     -- expression, needs layout after Foo
isExpressionLayoutKeyword :: TokenKind -> Bool
isExpressionLayoutKeyword = \case
  TokKeyword KwInterface -> True
  TokKeyword KwStruct -> True
  _ -> False

-- | Check if a token is a constructor ID.
isConId :: TokenKind -> Bool
isConId (TokConId _) = True
isConId (TokQConId _ _) = True
isConId _ = False

-- | State for tracking definition contexts.
data LayoutState = LayoutState
  { lsContext :: LayoutContext
  , lsAfterLayout :: Bool
  , lsInDefinitionHeader :: Bool  -- True after seeing class/instance ConId (wait for =)
  , lsAfterExprKeyword :: Bool    -- True after seeing interface/struct (layout after ConId)
  , lsPrevToken :: Maybe Token    -- Previous token for line comparison
  , lsFromNewLine :: Bool         -- True if current token started on a new line
  }

-- | Process a token stream according to layout rules.
--
-- Implements the L function from Haskell 2010 Report Section 10.3.
processLayout :: [Token] -> [Token]
processLayout tokens = go (LayoutState [] False False False Nothing False) tokens
  where
    go :: LayoutState -> [Token] -> [Token]
    go st ts = case ts of
      [] -> closeAll (lsContext st)

      (t:rest)
        -- Handle EOF specially - close all contexts and emit EOF
        -- But if we're expecting a layout block, emit an empty block first
        | TokEOF <- tokKind t ->
            if lsAfterLayout st
            then virtualLBrace t : virtualRBrace t : closeAll (lsContext st) ++ [t]
            else closeAll (lsContext st) ++ [t]

        -- After a layout keyword, expect a brace or start implicit block
        | lsAfterLayout st -> case tokKind t of
            TokPunct PunctLBrace ->
              -- Explicit brace: push 0 context
              t : go st { lsContext = 0 : lsContext st, lsAfterLayout = False, lsPrevToken = Just t } rest

            _ ->
              -- Start implicit block at this token's column
              let col = posColumn (spanBegin (tokSpan t))
                  ctx = lsContext st
                  newCtx = col : ctx
                  -- After inserting virtual brace, check if this token is a keyword
                  newState = st { lsContext = newCtx, lsAfterLayout = False, lsAfterExprKeyword = False, lsPrevToken = Just t }
                  -- Check if this token is a layout keyword
                  newState'
                    | isLayoutKeyword (tokKind t) =
                        newState { lsAfterLayout = True }
                    | isModuleLayoutKeyword (tokKind t) = case rest of
                        (next:_) | isVerilogKeyword (tokKind next) ->
                          newState { lsAfterLayout = False }  -- module verilog uses explicit braces
                        _ ->
                          newState { lsAfterLayout = True }  -- regular module triggers layout
                    | isExpressionLayoutKeyword (tokKind t) = case rest of
                        (next:_) | isConId (tokKind next) ->
                          newState { lsAfterExprKeyword = True }
                        _ ->
                          newState { lsAfterLayout = True }
                    | isContextualLayoutKeyword (tokKind t) = case rest of
                        (next:_) | isConId (tokKind next) ->
                          newState { lsInDefinitionHeader = True }
                        _ ->
                          newState { lsAfterLayout = True }
                    | otherwise = newState
              in if col > currentIndent ctx
                 then virtualLBrace t : t : go newState' rest
                 else -- Empty block
                      virtualLBrace t : virtualRBrace t : go st { lsAfterLayout = False, lsAfterExprKeyword = False } ts

        -- At start of line, check indentation first (insert semicolons/close braces)
        -- Then process the token through keyword checks
        | startsLine t st ->
            let col = posColumn (spanBegin (tokSpan t))
            in handleIndent col st { lsFromNewLine = True } t rest

        -- Tokens not at start of line go through processToken directly
        | otherwise -> processToken st { lsFromNewLine = False } t rest

    -- Handle indentation at start of line
    -- After inserting virtual tokens, re-process the token through main loop
    handleIndent :: Int -> LayoutState -> Token -> [Token] -> [Token]
    handleIndent col st t rest = case lsContext st of
      [] -> processToken st t rest

      (m : ms)
        | m == 0 ->
            -- In explicit block, no layout processing
            processToken st t rest

        | col == m ->
            -- Same indentation: insert semicolon, then re-process token
            -- But skip if:
            -- 1. Previous token was already an explicit semicolon
            -- 2. Current token is a continuation keyword (else, then, in, of)
            --    These keywords never start a new statement, so inserting a
            --    semicolon before them would always cause a parse error.
            case lsPrevToken st of
              Just prev | TokPunct PunctSemi <- tokKind prev ->
                processToken st t rest
              _ | isContinuationKeyword (tokKind t) ->
                processToken st t rest
              _ ->
                virtualSemi t : processToken st t rest

        | col < m ->
            -- Less indented: close this context and retry
            -- Update lsPrevToken to the virtual rbrace so that semicolon insertion
            -- doesn't get confused by an explicit semicolon that was inside the closed block
            let vbrace = virtualRBrace t
            in vbrace : handleIndent col st { lsContext = ms, lsPrevToken = Just vbrace } t rest

        | otherwise ->
            -- More indented: continue in current context
            processToken st t rest

    -- Process a token through keyword checks (called after handling indentation)
    processToken :: LayoutState -> Token -> [Token] -> [Token]
    processToken st t rest
      -- Check for = after definition header (class/instance Name)
      | lsInDefinitionHeader st, TokPunct PunctEqual <- tokKind t =
          t : go st { lsInDefinitionHeader = False, lsAfterLayout = True, lsPrevToken = Just t } rest

      -- Check for ConId after interface/struct
      -- Only trigger layout if the NEXT token is on a new line (expression case)
      -- If next token is on same line, it's likely a definition with type vars - wait for =
      | lsAfterExprKeyword st, isConId (tokKind t) =
          case rest of
            (next:_) | startsNewLine t next ->
              -- Next token on new line: expression body, trigger layout
              t : go st { lsAfterExprKeyword = False, lsAfterLayout = True, lsPrevToken = Just t } rest
            _ ->
              -- Next token on same line: definition, wait for =
              t : go st { lsAfterExprKeyword = False, lsInDefinitionHeader = True, lsPrevToken = Just t } rest

      -- Check for layout-triggering keywords
      | isLayoutKeyword (tokKind t) =
          t : go st { lsAfterLayout = True, lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest

      -- Check for 'module' keyword - triggers layout unless followed by 'verilog'
      | isModuleLayoutKeyword (tokKind t) =
          case rest of
            (next:_) | isVerilogKeyword (tokKind next) ->
              -- module verilog: no layout (uses explicit braces)
              t : go st { lsAfterLayout = False, lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest
            _ ->
              -- regular module: trigger layout
              t : go st { lsAfterLayout = True, lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest

      -- Check for expression layout keywords (interface/struct) - layout after ConId
      | isExpressionLayoutKeyword (tokKind t) =
          case rest of
            (next:_) | isConId (tokKind next) ->
              -- interface/struct followed by ConId: layout after the ConId
              t : go st { lsAfterExprKeyword = True, lsInDefinitionHeader = False, lsPrevToken = Just t } rest
            (next:_) | TokPunct PunctLParen <- tokKind next ->
              -- interface/struct followed by ( : kind annotation, definition header
              t : go st { lsInDefinitionHeader = True, lsAfterLayout = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest
            _ ->
              -- interface/struct NOT followed by ConId or (: layout immediately
              t : go st { lsAfterLayout = True, lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest

      -- Check for contextual layout keywords (only trigger if NOT followed by conId)
      | isContextualLayoutKeyword (tokKind t) =
          case rest of
            (next:_) | isConId (tokKind next) ->
              t : go st { lsInDefinitionHeader = True, lsAfterLayout = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest
            _ ->
              t : go st { lsAfterLayout = True, lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest

      -- Explicit braces
      | TokPunct PunctLBrace <- tokKind t =
          t : go st { lsContext = 0 : lsContext st, lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest

      | TokPunct PunctRBrace <- tokKind t =
          case lsContext st of
            (0 : ctx') -> t : go st { lsContext = ctx', lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest
            _ -> t : go st { lsInDefinitionHeader = False, lsAfterExprKeyword = False, lsPrevToken = Just t } rest

      -- 'in' keyword closes implicit layout contexts (for let/letseq blocks)
      -- Only close if 'in' is on the SAME line as previous token (no indentation check happened)
      -- If 'in' is on a new line, the indentation check already closed the necessary contexts
      | TokKeyword KwIn <- tokKind t =
          if lsFromNewLine st
          then -- Token came from a new line: indentation already handled, just emit 'in'
            t : go st { lsPrevToken = Just t } rest
          else -- Same line: close one implicit context
            closeForIn st t rest

      -- Regular token
      | otherwise =
          t : go st { lsAfterExprKeyword = False, lsPrevToken = Just t } rest

    -- Close one implicit layout context for 'in' keyword, then emit 'in'
    closeForIn :: LayoutState -> Token -> [Token] -> [Token]
    closeForIn st t rest = case lsContext st of
      -- No context or explicit context: just emit 'in'
      [] -> t : go st { lsPrevToken = Just t } rest
      (0 : _) -> t : go st { lsPrevToken = Just t } rest
      -- Implicit context: close it and emit 'in'
      (_ : ctx') ->
        let vbrace = virtualRBrace t
        in vbrace : t : go st { lsContext = ctx', lsPrevToken = Just t } rest

    -- Close all remaining implicit contexts
    closeAll :: LayoutContext -> [Token]
    closeAll [] = []
    closeAll (0 : _) = []  -- Can't close explicit context without }
    closeAll (m : ms) =
      let dummySpan = noSpan
      in Token dummySpan TokVRBrace : closeAll ms

    -- Get current indentation level
    currentIndent :: LayoutContext -> Int
    currentIndent [] = 0
    currentIndent (m : _) = m

    -- Check if token starts a new line (compared to previous token in state)
    startsLine :: Token -> LayoutState -> Bool
    startsLine t st = case lsPrevToken st of
      Nothing -> True  -- First token
      Just prev -> startsNewLine prev t

    -- Check if second token is on a new line compared to first
    startsNewLine :: Token -> Token -> Bool
    startsNewLine prev next =
      posLine (spanBegin (tokSpan next)) > posLine (spanEnd (tokSpan prev))

-- | Create a virtual left brace token.
virtualLBrace :: Token -> Token
virtualLBrace ref = Token
  { tokSpan = tokSpan ref
  , tokKind = TokVLBrace
  }

-- | Create a virtual right brace token.
virtualRBrace :: Token -> Token
virtualRBrace ref = Token
  { tokSpan = tokSpan ref
  , tokKind = TokVRBrace
  }

-- | Create a virtual semicolon token.
virtualSemi :: Token -> Token
virtualSemi ref = Token
  { tokSpan = tokSpan ref
  , tokKind = TokVSemi
  }
