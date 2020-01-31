module VFileName where

import Eval
import PPrint

newtype VFileName = VFileName String

vfnString :: VFileName -> String
vfnString (VFileName s) = s

instance Show VFileName where
  show vfn = vfnString vfn

instance Hyper VFileName where
  hyper (VFileName s) y = hyper s y

instance PPrint VFileName where
  pPrint d p (VFileName s) = text s

