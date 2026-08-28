-- | Operator fixity resolution for Bluespec Classic and BSV.
--
-- After parsing a flat infix expression chain (e1 op1 e2 op2 ... eN),
-- `resolveOps` restructures it into the correct tree according to operator
-- precedences and associativities.
module Language.Bluespec.Fixity
  ( resolveOps
  , bluespecFixities
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)

import Language.Bluespec.Position (Located (..), mergeSpans)
import Language.Bluespec.Syntax

-- | Default Bluespec operator fixity table.
-- Derived from @src/Libraries/Base1/Prelude.bs@ fixity declarations.
bluespecFixities :: Map Text Fixity
bluespecFixities = Map.fromList
  -- Prelude.bs declarations
  [ ("$",   Fixity InfixR 0)
  , (":=",  Fixity InfixR 0)
  , ("||",  Fixity InfixR 2)
  , ("&&",  Fixity InfixR 3)
  , ("|",   Fixity InfixR 4)
  , ("&",   Fixity InfixR 5)
  , ("^",   Fixity InfixR 5)
  , ("~^",  Fixity InfixR 5)
  , ("^~",  Fixity InfixR 5)
  , ("==",  Fixity InfixN 6)
  , ("/=",  Fixity InfixN 6)
  , ("<=",  Fixity InfixN 6)
  , (">=",  Fixity InfixN 6)
  , ("<",   Fixity InfixN 6)
  , (">",   Fixity InfixN 6)
  , ("<<",  Fixity InfixN 7)
  , (">>",  Fixity InfixN 7)
  , ("++",  Fixity InfixR 8)
  , (":>",  Fixity InfixR 8)   -- Vector/List cons
  , ("+",   Fixity InfixL 10)
  , ("-",   Fixity InfixL 10)
  , ("*",   Fixity InfixL 11)
  , ("/",   Fixity InfixL 11)
  , ("%",   Fixity InfixL 11)
  , ("\x2218", Fixity InfixR 13)  -- ∘ (function composition)
  -- BSV-specific
  , (".",   Fixity InfixR 14)  -- field access / function composition
  , ("!!",  Fixity InfixL 9)
  , ("|||", Fixity InfixR 4)   -- ActionValue bitwise or
  , ("&&&", Fixity InfixR 5)   -- ActionValue bitwise and
  , ("+",   Fixity InfixL 10)
  , ("|>",  Fixity InfixR 15)  -- ActionSeq join
  , ("\x00BB", Fixity InfixR 12)  -- » (Push/Pull pipe)
  , ("+++", Fixity InfixR 8)   -- String concatenation
  ]

-- | Default fixity for unknown operators (left-assoc, prec 9).
defaultFixity :: Fixity
defaultFixity = Fixity InfixL 9

-- | Look up the fixity of an operator name.
lookupFixity :: Text -> Map Text Fixity -> Fixity
lookupFixity name table = Map.findWithDefault defaultFixity name table

-- | Extract text from an Op (handles OpSym and backtick idents).
opText :: Op -> Text
opText (OpSym t)             = t
opText (OpIdent (Located _ qi)) = identText (qualIdent qi)

-- | Resolve operator precedence in a flat infix chain.
--
-- Given the leftmost expression and a list of @(operator, operand)@ pairs,
-- returns the correctly parenthesised expression tree.
--
-- Uses the standard precedence-climbing algorithm.
resolveOps
  :: Map Text Fixity
  -> LExpr
  -> [(Located Op, LExpr)]
  -> LExpr
resolveOps table e ops = fst (climb 0 e ops)
  where
    climb :: Int -> LExpr -> [(Located Op, LExpr)] -> (LExpr, [(Located Op, LExpr)])
    climb minPrec lhs [] = (lhs, [])
    climb minPrec lhs input@((op, rhs) : rest)
      | opPrec < minPrec = (lhs, input)
      | otherwise =
          let -- Right-assoc: recurse at same level; Left/Non: require strictly higher
              nextPrec = case opAssoc of
                InfixR -> opPrec
                _      -> opPrec + 1
              (rhs', rest')  = climb nextPrec rhs rest
              sp              = mergeSpans (locSpan lhs) (locSpan rhs')
              combined        = Located sp (EInfix lhs op rhs')
          in climb minPrec combined rest'
      where
        Fixity opAssoc opPrec = lookupFixity (opText (locVal op)) table
