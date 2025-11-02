{-# LANGUAGE DeriveAnyClass #-}

module Literal(Literal(..)) where

import GHC.Generics (Generic)
import Eval
import IntLit
import PPrint
import PVPrint

data Literal
        = LString String
        | LChar Char
        | LInt IntLit
        | LReal Double
        | LPosition -- a position literal is a placeholder for the position in CLiteral
        deriving (Eq, Ord, Show, Generic, NFData)

instance PPrint Literal where
    pPrint _ _ (LString s) = text (show s)
    pPrint _ _ (LChar c) = text (show c)
    pPrint d p (LInt i) = pPrint d p i
    pPrint d p (LReal r) = pPrint d p r
    pPrint _ _ LPosition = text ("<Position>")

instance PVPrint Literal where
    pvPrint _ _ (LString s) = text (show s)
    pvPrint _ _ (LChar c) = text (show [c])
    pvPrint d p (LInt i) = pvPrint d p i
    pvPrint d p (LReal r) = pvPrint d p r
    pvPrint _ _ LPosition = text ("<Position>")
