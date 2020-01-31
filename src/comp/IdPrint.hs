module IdPrint(
          pvpPId, pvpId, pfpId, ppId, ppConId, ppVarId, mkUId,
          getBSVIdString
         ) where

import Data.Char(isDigit)

import Id
import Util(dbgLevel)
import Lex(isIdChar, isSym)
import ErrorUtil(internalError)
import PreStrings(fsEmpty, fsPrelude, fsPreludeBSV)
import Classic
import PPrint
import PVPrint
import IOUtil(progArgs)

show_qual = "-show-qualifiers" `elem` progArgs

local_show id =
    let
        pos = getIdPosition id
        mfs = getIdQualString id
        fs = getIdBaseString id
        str = show pos ++ " " ++
                show mfs ++ " " ++
                show fs
    in str

instance PPrint Id where
    pPrint PDDebug _ i = text (local_show i)
                -- <> text(" props: " ++  show (getIdProps i ))
    pPrint _ _ i =
        if (dbgLevel >= 1)
             then text ((getIdString i) ++
                        "_"  ++
                        (createPositionString (getIdPosition i)))
             else text (getIdString i)
--    pPrint _ _ i = text ((getIdString i) ++ "|" ++ (show (getIdPosition i)) ++ "|" ++ (show (getIdProps i)))
--    pPrint _ _ i = text ((getIdString i) ++ "|" ++ (show (getIdProps i)))

-- --------------------

instance PVPrint Id where
    pvPrint PDDebug _ i = text (show i)
    pvPrint PDNoqual _ i = text (getIdBaseString i)
    pvPrint _ _ i =
      let s = getBSVIdString i
      in text (if s=="not" then "!" else s)

pvpPId :: PDetail -> Id -> Doc
pvpPId d i =
    case getIdBaseString i of
    _   -> pvpId d i

pvpId :: PDetail -> Id -> Doc
pvpId PDDebug i = pvPrint PDDebug 0 i
pvpId PDNoqual i = pvPrint PDNoqual 0 i
pvpId d i =
    case getIdBaseString i of
    "->" -> text "(->)"
    ":=" -> text "<="
    "not" -> text "!"
    s@(c:_) | isDigit c -> text s
    c:_ | isIdChar c -> text (getBSVIdString i)
    _ -> text ("("++getBSVIdString i++")")

-- hack: suppress the package name for operators
getBSVIdString :: Id -> String
getBSVIdString a = (getBSVIdStringz a)
getBSVIdStringz :: Id -> String
getBSVIdStringz a
    | getIdBase a == fsEmpty = internalError "CVPrint.getIdStr: empty identifier"
    | getIdQual a == fsEmpty = getIdBaseStringz a
    | not (isIdChar (head (getIdBaseStringz a))) = getIdBaseStringz a -- operators
    | (not show_qual) && (getIdQual a == fsPrelude) =
          getIdBaseStringz a  -- suppress "Prelude::" unless flag is on
    | (not show_qual) && (getIdQual a == fsPreludeBSV) =
          getIdBaseStringz a  -- suppress "Prelude::" unless flag is on
    | otherwise = getIdQualString a ++ "::" ++ getIdBaseStringz a

getIdBaseStringz :: Id -> String
getIdBaseStringz a =
    let s = getIdBaseString a
    in if (not (isEse()) || length s < 7) then s
       else if (take 7 s == "ese_id_" || take 7 s == "Ese_id_") then drop 7 s
       else s

-- --------------------

pfpId :: PDetail -> Id -> Doc
pfpId = if isClassic() then ppId else pvpId

ppId :: PDetail -> Id -> Doc
ppId PDDebug i = pPrint PDDebug 0 i
ppId d i =
    if (dbgLevel >= 1)
    then case (getIdBaseString i) of
          "->" -> text "(->)"                          -- arrow
          s@(c:_) | isDigit c -> text( s ++ "_" ++ (createPositionString (getIdPosition i)))
          c:_ | isIdChar c -> text ((getIdString i) ++ "_" ++ (createPositionString (getIdPosition i)))
          '$':c:_ | isIdChar c -> text (getIdString i) -- task names
          _ -> text ("(" ++ (getIdString i) ++ "_" ++ (createPositionString (getIdPosition i)))
    else case (getIdBaseString i) of
          "->" -> text "(->)"                          -- arrow
          s@(c:_) | isDigit c -> text s                -- numbers
          c:_ | isIdChar c -> text (getIdString i)     -- identifiers
          '$':c:_ | isIdChar c -> text (getIdString i) -- task names
          _ -> text ("("++getIdString i++")")          -- infix operators

ppVarId :: PDetail -> Id -> Doc
ppVarId PDDebug i = pPrint PDDebug 0 i
ppVarId d i =
    if (dbgLevel >= 1)
    then case (getIdBaseString i) of
    s | all isSym s -> text ("("++ (getIdStringOp i) ++ (createPositionString (getIdPosition i)) ++
                             ")") -- infix operators
    '$':c:_ | isIdChar c -> text ((getIdStringVar i) ++ (createPositionString (getIdPosition i)))
    _ -> text ((getIdStringVar i) ++ (createPositionString (getIdPosition i)))
    else case (getIdBaseString i) of
    s | all isSym s -> text ("("++getIdStringOp i ++ ")") -- infix operators
    '$':c:_ | isIdChar c -> text (getIdStringVar i) -- task names
    _ -> text (getIdStringVar i)

ppConId :: PDetail -> Id -> Doc
ppConId PDDebug i = pPrint PDDebug 0 i
ppConId d i = -- text ( "props:" ++ show (getIdProps i)) <>
    case (getIdBaseString i) of
    "->" -> text "(->)"                -- arrow
    s@(c:_) | all isDigit s -> text s  -- numbers
    _ -> text (getIdStringCon i)       -- constructor-identifiers

-- These used to encode properties in .bi files
getIdStringCon = getIdString
getIdStringVar = getIdString
getIdStringOp  = getIdString

-- --------------------

instance PPrint IdProp where
    pPrint d _ (IdPInlinedPositions poss) =
        pparen True (text "IdPInlinedPositions" <+> pPrint d 0 poss)
    pPrint _ _ prop = text (show prop)

{-
instance PVPrint IdProp where
    pvPrint d _ (IdPInlinedPositions poss) =
        pparen True (text "IdPInlinedPositions" <+> pvPrint d 0 poss)
    pvPrint _ _ prop = text (show prop)
-}

