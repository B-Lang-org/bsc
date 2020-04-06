{-# LANGUAGE CPP #-}
module IfcBetterInfo(
                     BetterInfo(..),
                     extractMethodInfo,
                     matchMethodName,
                     noMethodInfo
                    ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Flags(Flags)
import SymTab
import Id
import Pragma
import PPrint
import IdPrint
import VModInfo
import FStringCompat(mkFString)
import ISyntax
import IConv(iConvT)
-- import Util(traces)


-- module for extracting "better" method argument names and types from the symbol table
-- This information is used by IExpand for populating the VModInfo
-- and for recording the types of external method ports
data BetterInfo = BetterMethodInfo
                  { mi_id     :: Id, -- method Id
                    mi_result :: VPort, -- possible rename for method result
                    mi_ready  :: VPort, -- for ready signal
                    mi_enable :: VPort, -- for enable signal
                    mi_prefix :: Id,    -- default prefix for arguments (which are not found in classic)
                    mi_args   :: [Id],          -- for arguments
                    mi_orig_type :: Maybe IType -- original (unwrapped) field type
                  }
                -- XXX Note that the following are unused
                -- XXX (this package needs re-thinking)
                | BetterClockInfo
                  { ci_id :: Id
                  }
                | BetterResetInfo
                  { ri_id :: Id
                  }
                | BetterInoutInfo
                  { io_id :: Id
                  }

-- utilitity comparison function for use in lookup/find
matchMethodName :: Id ->  BetterInfo -> Bool
matchMethodName id mn = qualEq id (mi_id mn)

-- creates a basic method remaing
noMethodInfo :: Id -> BetterInfo
noMethodInfo fieldId = BetterMethodInfo {mi_id = fieldId,
                                     mi_result = id_to_vPort fieldId,
                                     mi_ready  = id_to_vPort $ mkRdyId fieldId,
                                     mi_enable = id_to_vPort $ mkEnableId fieldId,
                                     mi_prefix = fieldId,
                                     mi_args = [],
                                     mi_orig_type = Nothing
                                  }


instance PPrint BetterInfo  where
    pPrint d i info = (text "methodNames") <> ppId d (mi_id info) <> equals <> braces
                        ( printMaybe d i "Result:" (mi_result info) <>
                          printMaybe d i "Ready:" (mi_ready info) <>
                          printMaybe d i "Enable:" (mi_enable info) <>
                          text "Prefix:" <> pPrint d i (mi_prefix info) <>
                          text "Args:" <>  pPrint d i (mi_args info) <>
                          printMaybe d i "Original type:" (mi_orig_type info)
                        )

printMaybe :: PPrint a => PDetail -> Int -> String -> a -> Doc
printMaybe d i str x =  text str <> pPrint d i x




-- this function pulls the method info from an interface
extractMethodInfo :: Flags -> SymTab -> Id  -> [BetterInfo]
extractMethodInfo = genBetterInfoFromIfc

genBetterInfoFromIfc :: Flags -> SymTab -> Id -> [BetterInfo]
genBetterInfoFromIfc flags symbolTable ifcId =
    -- traces("GBN ifcId: " ++ ppReadable ifcId) $
    -- traces("GBN methFields: " ++ ppReadable methFields) $
    -- traces("GBN result: " ++ ppReadable props) $
    props
    where
    -- Get method names and associated field infos
    methIds    = getIfcFieldNames symbolTable ifcId
    methFields :: [ (Id,Maybe FieldInfo) ]
    methFields = zip methIds $ map (findFieldInfo symbolTable ifcId) methIds
    --
    -- covert the information to to IfcBetterName
    props = map (fieldInfoToBetterInfo flags symbolTable) methFields

fieldInfoToBetterInfo :: Flags -> SymTab -> (Id,Maybe FieldInfo) -> BetterInfo
fieldInfoToBetterInfo flags symTab (fieldId, Nothing) = noMethodInfo fieldId
fieldInfoToBetterInfo flags symTab (fieldId, Just fi) =
    BetterMethodInfo {mi_id = fieldId,
                      mi_result = maybe (id_to_vPort fieldId) (str_to_vPort) mres,
                      mi_ready  = maybe (id_to_vPort $ mkRdyId fieldId) str_to_vPort mrdy,
                      mi_enable = maybe (id_to_vPort $ mkEnableId fieldId) str_to_vPort  men,
                      mi_prefix = maybe fieldId (setIdBaseString fieldId) mprefix,
                      mi_args = args,
                      mi_orig_type = fmap (iConvT flags symTab) (fi_orig_type fi)
               }
    where prags   = fi_pragmas fi
          (mprefix,mres,mrdy,men,rawargs,_,_) = getMethodPragmaInfo prags
          args    = genArgNames mprefix fieldId rawargs


-- Create a list of Ids for method argument names
-- Used by IExpand  thru IfcbetterNames   maybe move it here
-- Note that this only uses IPrefixStr and iArgNames, which must be
-- kept on the FieldInfo in the SymTab
genArgNames :: Maybe String -> Id -> [Id] -> [Id]
genArgNames mprefix fieldId ids = map (addPrefix mprefix fieldId)  ids
    where addPrefix :: Maybe String -> Id -> Id -> Id
          addPrefix Nothing fid aid   = mkUSId fid aid
          addPrefix (Just "") _ aid   = aid
          addPrefix (Just pstr) _ aid = mkIdPre (mkFString $ pstr ++ "_" ) aid
