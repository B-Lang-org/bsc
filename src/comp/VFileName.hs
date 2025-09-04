module VFileName where

import Eval
import PPrint

newtype VFileName = VFileName String

vfnString :: VFileName -> String
vfnString (VFileName s) = s

instance Show VFileName where
  show vfn = vfnString vfn

instance NFData VFileName where
  rnf (VFileName s) = rnf s `seq` ()

instance PPrint VFileName where
  pPrint d p (VFileName s) = text s

