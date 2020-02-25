module Assump(Assump(..)) where
import Id
import Scheme
import Subst
import PPrint
import Eval

data Assump
        = Id :>: Scheme
        deriving (Show, Eq)

instance PPrint Assump where
    pPrint d p (i :>: s) = pparen (p > 0) $ pPrint d 0 i <+> text ":>:" <+> pPrint d 0 s

instance Types Assump where
    apSub s (i :>: sc) = i :>: (apSub s sc)
    tv      (i :>: sc) = tv sc

instance Hyper Assump where
    hyper (i :>: sc) y = hyper2 i sc y
