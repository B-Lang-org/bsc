{-# LANGUAGE DeriveAnyClass #-}

module Assump(Assump(..)) where

import Id
import Scheme
import Subst
import PPrint
import Eval
import GHC.Generics (Generic)

data Assump
        = Id :>: Scheme
        deriving (Show, Eq, Generic, NFData)

instance PPrint Assump where
    pPrint d p (i :>: s) = pparen (p > 0) $ pPrint d 0 i <+> text ":>:" <+> pPrint d 0 s

instance Types Assump where
    apSub s (i :>: sc) = i :>: (apSub s sc)
    tv      (i :>: sc) = tv sc
