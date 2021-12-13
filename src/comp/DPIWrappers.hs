module DPIWrappers ( genDPIWrappers ) where

import ForeignFunctions(ForeignFunction(..), isPoly)
import CCSyntax(CCFragment)
import Position(getPosition)
import Error(ErrorHandle, bsError, ErrMsg(EGeneric))
import Flags(Flags(..))

genDPIWrappers :: ErrorHandle ->
                  Flags -> String -> [String] -> [ForeignFunction] ->
                  IO [CCFragment]
genDPIWrappers errh flags prefix blurb ffs =
  do files <- mapM (writeWrapper errh flags prefix blurb) ffs
     return $ concat files

writeWrapper :: ErrorHandle ->
                Flags -> String -> [String] -> ForeignFunction ->
                IO [CCFragment]
writeWrapper errh flags prefix blurb (FF name rt arg_types) =
  if (isPoly rt || any isPoly arg_types)
  then do
    -- Polymorphic types require a wrapper
    -- XXX When we implement wrapper generation,
    -- XXX remember to add it to 'getGenFs' in 'Depend.hs'.
    let pos = getPosition name
        msg = "Polymorphic types are not yet supported with DPI"
    bsError errh [(pos, EGeneric msg)]
  else do
    -- If there are no polymorphic types, then no wrapper is needed
    return []
