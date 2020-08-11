module PFPrint(PPrint(..), module Pretty, PDetail(..),
        ppReadable, ppReadableIndent, ppAll, ppDebug, ppString, pp80,
        pparen, pfPrint, sepList, maxPrec,
        PVPrint(..),
        pvpReadable, pvpReadableIndent, pvpAll, pvpDebug, pvpString, pvpStringNQ, pvp80,
        pvparen,
        pfpReadable, pfpReadableIndent, pfpAll, pfpDebug, pfpString, pfp80,
        pfparen, ppDoc
        ) where
import Classic
-- import Debug.Trace
import PPrint
import PVPrint
import Pretty -- already exported by PPrint, but needed in order to export again

pfpReadable :: (PPrint a, PVPrint a) => a -> String
pfpReadable a = if isClassic() then ppReadable a else pvpReadable a

pfpReadableIndent :: (PPrint a, PVPrint a) => Int -> a -> String
pfpReadableIndent a = if isClassic() then ppReadableIndent a else pvpReadableIndent a

pfpAll, pfpDebug, pfpString, pfp80 :: (PPrint a, PVPrint a) => a -> String
pfpAll a = if isClassic() then ppAll a else pvpAll a
pfpDebug a = if isClassic() then ppDebug a else pvpDebug a
pfpString a = if isClassic() then ppString a else pvpString a
pfp80 a = if isClassic() then pp80 a else pvp80 a

pfparen :: Bool -> Doc -> Doc
pfparen = if isClassic() then pparen else pvparen

pfPrint :: (PPrint a, PVPrint a) => PDetail -> Int -> a -> Doc
pfPrint = if isClassic() then pPrint else pvPrint
