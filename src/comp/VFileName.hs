module VFileName where

import Eval(NFData(..), rnf)
import PPrint

newtype VFileName = VFileName String

vfnString :: VFileName -> String
vfnString (VFileName s) = s

instance Show VFileName where
  show vfn = vfnString vfn

instance NFData VFileName where
  rnf (VFileName s) = rnf s

instance PPrint VFileName where
  pPrint d p (VFileName s) = text s

