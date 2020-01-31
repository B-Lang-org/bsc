module Fixity(Fixity(..), defaultFixity) where

data Fixity 
	= FInfixl Int | FInfixr Int | FInfix Int
	| FPrefix
	| FInfixa Int						-- used only in printing to indicate assoc oper
    deriving (Eq, Ord, Show)

defaultFixity :: Fixity
defaultFixity = FInfixl 15
