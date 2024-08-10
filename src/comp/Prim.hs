{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
module Prim(
            PrimOp(..),
            toPrim,
            toWString,
            stringSize,
            writePrimOp, readPrimOp,
            PrimResult(..), PrimArg(..)
            ) where

import Numeric(floatToDigits)
import Eval(NFData(..))
import PPrint
import Id
import Position
import Log2
import IntegerUtil
import RealUtil hiding (log2, log10)
import qualified RealUtil as R (log2,log10)
import ErrorUtil(internalError)
import Error(ErrMsg(..))
import qualified Data.Generics as Generic

data PrimOp =
          PrimAdd
        | PrimSub
        | PrimAnd
        | PrimOr
        | PrimXor

        | PrimMul

        | PrimQuot
        | PrimRem

        | PrimSL
        | PrimSRL
        | PrimSRA

        | PrimInv
        | PrimNeg

        | PrimEQ

        | PrimULE
        | PrimULT

        | PrimSLE
        | PrimSLT

        | PrimSignExt
        | PrimZeroExt

        | PrimTrunc

        | PrimExtract
        | PrimConcat
        | PrimSplit

        | PrimBNot
        | PrimBAnd
        | PrimBOr

        | PrimInoutCast
        | PrimInoutUncast

        | PrimMethod

        | PrimIf
        | PrimMux
        | PrimPriMux

        | PrimFmtConcat

        -- Only in ATS
        -- use: PrimCase e d c1 e1 c2 e2 ... cn en
        -- e is the scrutinized expression, d is the default value, (ck, ek) forms a case arm
        | PrimCase

        -- Only used in intermediate code
        -- primSelect @k @m @n e  selects k bits at position m from n bits
        -- primSelect :: \/ k, m, n :: * -> Bit n -> Bit k
        | PrimSelect

        -- primitives without hardware representation
        | PrimIntegerToBit
        | PrimIntegerToUIntBits
        | PrimIntegerToIntBits
        | PrimBitToInteger -- XXX dangerous
        | PrimIntegerToString

        -- must be called on compile-time values
        | PrimIntBitsToInteger
        | PrimUIntBitsToInteger

        | PrimIsStaticInteger
        | PrimAreStaticBits

        | PrimValueOf
        | PrimStringOf

        | PrimWhen
        | PrimWhenPred -- takes abstract predicate

        | PrimOrd
        | PrimChr

        -- primRange lo hi x, promises lo <= x <= hi
        | PrimRange

        | PrimError
        | PrimGenerateError
        | PrimMessage
        | PrimWarning
        | PrimPoisonedDef

        | PrimDynamicError

        | PrimStringConcat
        | PrimStringToInteger
        | PrimStringEQ
        | PrimStringLength

        | PrimStringSplit
        | PrimStringCons

        | PrimCharToString
        | PrimStringToChar
        | PrimCharOrd
        | PrimCharChr

        | PrimJoinActions
        | PrimNoActions
        | PrimExpIf     -- "split shallow"
        | PrimNoExpIf   -- "nosplit shallow"
        | PrimSplitDeep
        | PrimNosplitDeep
        | PrimAddRules
        | PrimModuleBind
        | PrimModuleReturn
        | PrimModuleFix
        | PrimModuleClock
        | PrimModuleReset
        | PrimBuildModule
        | PrimCurrentClock
        | PrimCurrentReset
        | PrimSameFamilyClock
        | PrimIsAncestorClock
        | PrimChkClockDomain
        | PrimClockEQ
        | PrimClockOf
        | PrimClocksOf
        | PrimNoClock
        | PrimResetEQ
        | PrimResetOf
        | PrimResetsOf
        | PrimNoReset
        | PrimResetUnassertedVal
        | PrimJoinRules
        | PrimJoinRulesPreempt
        | PrimJoinRulesUrgency
        | PrimJoinRulesExecutionOrder
        | PrimJoinRulesMutuallyExclusive
        | PrimJoinRulesConflictFree
        | PrimNoRules
        | PrimRule
        -- PrimAddSchedPragmas :: [SchedulePragma] -> Rules -> Rules
        | PrimAddSchedPragmas

        | PrimGetName
        -- primStateName :: Name -> Module b -> Module b
        -- This primitive is used to name state components.
        -- The first argument is an abstract name that is added to
        -- the names of state elements instantiated by the second argument.
        | PrimStateName
        | PrimGetModuleName

        | PrimJoinNames
        | PrimExtendNameInteger
        | PrimGetNamePosition
        | PrimGetNameString
        | PrimMakeName

        -- primStateAttrib :: Attributes -> Module b -> Module b
        -- This primitive is used to add attributes to submod instantiations.
        -- The first argument is an abstract list of attributes.
        | PrimStateAttrib

        | PrimNoPosition
        | PrimPrintPosition
        | PrimGetStringPosition
        | PrimSetStringPosition
        | PrimGetEvalPosition

        -- environment
        | PrimGenC
        | PrimGenVerilog
        | PrimGenModuleName

        -- elaboration-time file IO
        | PrimOpenFile
        | PrimCloseHandle
        | PrimHandleIsEOF
        | PrimHandleIsOpen
        | PrimHandleIsClosed
        | PrimHandleIsReadable
        | PrimHandleIsWritable
        | PrimSetHandleBuffering
        | PrimGetHandleBuffering
        | PrimFlushHandle
        | PrimWriteHandle
        | PrimReadHandleLine
        | PrimReadHandleChar

        -- reflective type primitives
        | PrimTypeOf
        | PrimPrintType
        | PrimTypeEQ
        | PrimIsIfcType

        -- type-tracking primitive
        | PrimSavePortType

        -- compile time numbers
        | PrimIntegerAdd
        | PrimIntegerSub
        | PrimIntegerNeg
        | PrimIntegerMul
        | PrimIntegerDiv
        | PrimIntegerMod
        | PrimIntegerExp
        | PrimIntegerLog2
        | PrimIntegerLog10
        | PrimIntegerQuot
        | PrimIntegerRem

        | PrimIntegerEQ
        | PrimIntegerLE
        | PrimIntegerLT

        -- Real numbers: Show
        | PrimRealToString
        -- Real numbers: Literal
        | PrimIntegerToReal
        -- Real numbers: Eq and Ord
        | PrimRealEQ
        | PrimRealLE
        | PrimRealLT
        -- Real numbers: Arith
        | PrimRealAdd
        | PrimRealSub
        | PrimRealNeg
        | PrimRealMul
        | PrimRealDiv
        | PrimRealAbs
        | PrimRealSignum
        | PrimRealExpE
        | PrimRealPow
        | PrimRealLogE
        | PrimRealLogBase
        | PrimRealLog2
        | PrimRealLog10
        -- Real numbers: Bits
        | PrimRealToBits
        | PrimBitsToReal
        -- Real numbers: Trig
        | PrimRealSin
        | PrimRealCos
        | PrimRealTan
        | PrimRealSinH
        | PrimRealCosH
        | PrimRealTanH
        | PrimRealASin
        | PrimRealACos
        | PrimRealATan
        | PrimRealASinH
        | PrimRealACosH
        | PrimRealATanH
        | PrimRealATan2
        -- Real numbers: Sqrt
        | PrimRealSqrt
        -- Real numbers: Rounding
        | PrimRealTrunc
        | PrimRealCeil
        | PrimRealFloor
        | PrimRealRound
        -- Real numbers: Introspection
        | PrimSplitReal
        | PrimDecodeReal
        | PrimRealToDigits
        | PrimRealIsInfinite
        | PrimRealIsNegativeZero

        | PrimSeq        -- args are eval in sequence
                        -- for side effects or strictness
        | PrimSeqCond   -- implicit-condition strictness
        | PrimUninitialized
        | PrimRawUninitialized -- error out with a use of an uninitialized value
        | PrimMarkArrayUninitialized -- mark array as uninitialized
        | PrimMarkArrayInitialized -- mark array as initialized
        | PrimUninitBitArray -- make an array of uninitialized bits
        | PrimIsBitArray -- is this Bit n represented as an array
        | PrimUpdateBitArray
        | PrimBuildUndefined -- build a type-appropriate undefined value
        | PrimRawUndefined -- create a "raw" undefined value
        | PrimIsRawUndefined -- test if a value is a "raw" undefined value
        | PrimImpCondOf -- XXX experimental
        | PrimArrayNew  -- Primitive array operators
        | PrimArrayLength
        | PrimArraySelect
        | PrimArrayUpdate
        | PrimArrayDynSelect
        | PrimArrayDynUpdate
        | PrimBuildArray -- only exists after IExpand and in ASyntax

        | PrimSetSelPosition

        | PrimGetParamName -- get the parameter name associated with the function value

        | PrimEQ3 -- === / Verilog case equality
        deriving (Eq, Ord, Show, Enum, Bounded, Generic.Data, Generic.Typeable)

-- Just some size, have to be coordinated with Prelude.bs
stringSize :: String -> Integer
stringSize s = toInteger (8 * length s)        -- in bytes as bits

toPrim :: Id -> PrimOp
toPrim i = tp (getIdBaseString i)                -- XXXXX
  where tp "primAdd" = PrimAdd
        tp "primSub" = PrimSub
        tp "primAnd" = PrimAnd
        tp "primOr"  = PrimOr
        tp "primXor" = PrimXor
        tp "primMul" = PrimMul
        tp "primQuot" = PrimQuot
        tp "primRem" = PrimRem
        tp "primSL"  = PrimSL
        tp "primSRL" = PrimSRL
        tp "primSRA" = PrimSRA
        tp "primInv" = PrimInv
        tp "primNeg" = PrimNeg
        tp "primEQ"  = PrimEQ
        tp "primEQ3" = PrimEQ3
        tp "primULE" = PrimULE
        tp "primULT" = PrimULT
        tp "primSLE" = PrimSLE
        tp "primSLT" = PrimSLT
        tp "primSignExt" = PrimSignExt
        tp "primZeroExt" = PrimZeroExt
        tp "primTrunc" = PrimTrunc
        tp "primExtractInternal" = PrimExtract
        tp "primConcat" = PrimConcat
        tp "primSplit" = PrimSplit
        tp "primBNot" = PrimBNot
        tp "primBAnd" = PrimBAnd
        tp "primBOr" = PrimBOr
        tp "primInoutCast" = PrimInoutCast
        tp "primInoutUncast" = PrimInoutUncast
        tp "primMethod" = PrimMethod
        tp "primIntegerToBit" = PrimIntegerToBit
        tp "primIntegerToUIntBits" = PrimIntegerToUIntBits
        tp "primIntegerToIntBits"  = PrimIntegerToIntBits
        tp "primBitToInteger" = PrimBitToInteger
        tp "primIntegerToString" = PrimIntegerToString
        tp "primUIntBitsToInteger" = PrimUIntBitsToInteger
        tp "primIntBitsToInteger"  = PrimIntBitsToInteger
        tp "primIsStaticInteger" = PrimIsStaticInteger
        tp "primAreStaticBits" = PrimAreStaticBits
        tp "primWhen" = PrimWhen
        tp "primValueOf" = PrimValueOf
        tp "primStringOf" = PrimStringOf
        tp "primOrd" = PrimOrd
        tp "primChr" = PrimChr
        tp "primIf" = PrimIf
        tp "primRange" = PrimRange
        tp "primError" = PrimError
        tp "primPoisonedDef" = PrimPoisonedDef
        tp "primGenerateError" = PrimGenerateError
        tp "primMessage" = PrimMessage
        tp "primWarning" = PrimWarning
        tp "primDynamicError" = PrimDynamicError

        tp "primJoinActions" = PrimJoinActions
        tp "primNoActions" = PrimNoActions
        tp "primExpIf" = PrimExpIf
        tp "primNoExpIf" = PrimNoExpIf
        tp "primSplitDeep" = PrimSplitDeep
        tp "primNosplitDeep" = PrimNosplitDeep
        tp "primAddRules" = PrimAddRules
        tp "primModuleBind" = PrimModuleBind
        tp "primModuleReturn" = PrimModuleReturn
        tp "primModuleFix" = PrimModuleFix
        tp "primModuleClock" = PrimModuleClock
        tp "primModuleReset" = PrimModuleReset
        tp "primBuildModule" = PrimBuildModule
        tp "primJoinRules" = PrimJoinRules
        tp "primJoinRulesPreempt" = PrimJoinRulesPreempt
        tp "primJoinRulesUrgency" = PrimJoinRulesUrgency
        tp "primJoinRulesExecutionOrder" = PrimJoinRulesExecutionOrder
        tp "primJoinRulesMutuallyExclusive" = PrimJoinRulesMutuallyExclusive
        tp "primJoinRulesConflictFree" = PrimJoinRulesConflictFree
        tp "primNoRules" = PrimNoRules
        tp "primRule" = PrimRule

        tp "primStringConcat" = PrimStringConcat
        tp "primStringToInteger" = PrimStringToInteger
        tp "primStringEQ" = PrimStringEQ
        tp "primStringLength" = PrimStringLength

        tp "primStringSplit" = PrimStringSplit
        tp "primStringCons" = PrimStringCons

        tp "primCharToString" = PrimCharToString
        tp "primStringToChar" = PrimStringToChar
        tp "primCharOrd" = PrimCharOrd
        tp "primCharChr" = PrimCharChr

        tp "primFmtConcat" = PrimFmtConcat
        tp "primCurrentClock" = PrimCurrentClock
        tp "primCurrentReset" = PrimCurrentReset
        tp "primSameFamilyClock" = PrimSameFamilyClock
        tp "primIsAncestorClock" = PrimIsAncestorClock
        tp "primChkClockDomain" = PrimChkClockDomain
        tp "primClockEQ" = PrimClockEQ
        tp "primClockOf" = PrimClockOf
        tp "primClocksOf" = PrimClocksOf
        tp "primNoClock" = PrimNoClock
        tp "primResetEQ" = PrimResetEQ
        tp "primResetOf" = PrimResetOf
        tp "primResetsOf" = PrimResetsOf
        tp "primNoReset" = PrimNoReset
        tp "primResetUnassertedVal" = PrimResetUnassertedVal

        tp "primGetName" = PrimGetName
        tp "primGetParamName" = PrimGetParamName
        tp "primStateName" = PrimStateName
        tp "primGetModuleName" = PrimGetModuleName
        tp "primJoinNames" = PrimJoinNames
        tp "primExtendNameInteger" = PrimExtendNameInteger
        tp "primGetNamePosition" = PrimGetNamePosition
        tp "primGetNameString" = PrimGetNameString
        tp "primMakeName" = PrimMakeName

        tp "primStateAttrib" = PrimStateAttrib

        tp "primNoPosition" = PrimNoPosition
        tp "primPrintPosition" = PrimPrintPosition
        tp "primGetStringPosition" = PrimGetStringPosition
        tp "primSetStringPosition" = PrimSetStringPosition
        tp "primGetEvalPosition" = PrimGetEvalPosition

        tp "primGenC" = PrimGenC
        tp "primGenVerilog" = PrimGenVerilog
        tp "primGenModuleName" = PrimGenModuleName

        tp "primOpenFile" = PrimOpenFile
        tp "primCloseHandle" = PrimCloseHandle
        tp "primHandleIsEOF" = PrimHandleIsEOF
        tp "primHandleIsOpen" = PrimHandleIsOpen
        tp "primHandleIsClosed" = PrimHandleIsClosed
        tp "primHandleIsReadable" = PrimHandleIsReadable
        tp "primHandleIsWritable" = PrimHandleIsWritable
        tp "primSetHandleBuffering" = PrimSetHandleBuffering
        tp "primGetHandleBuffering" = PrimGetHandleBuffering
        tp "primFlushHandle" = PrimFlushHandle
        tp "primWriteHandle" = PrimWriteHandle
        tp "primReadHandleLine" = PrimReadHandleLine
        tp "primReadHandleChar" = PrimReadHandleChar

        tp "primTypeOf" = PrimTypeOf
        tp "primPrintType" = PrimPrintType
        tp "primTypeEQ" = PrimTypeEQ
        tp "primIsIfcType" = PrimIsIfcType

        tp "primSavePortType" = PrimSavePortType

        tp "primSeq" = PrimSeq
        tp "primSeqCond" = PrimSeqCond

        tp "primIntegerAdd" = PrimIntegerAdd
        tp "primIntegerSub" = PrimIntegerSub
        tp "primIntegerNeg" = PrimIntegerNeg
        tp "primIntegerMul" = PrimIntegerMul
        tp "primIntegerDiv" = PrimIntegerDiv
        tp "primIntegerMod" = PrimIntegerMod
        tp "primIntegerQuot" = PrimIntegerQuot
        tp "primIntegerRem" = PrimIntegerRem
        tp "primIntegerExp" = PrimIntegerExp
        tp "primIntegerLog2" = PrimIntegerLog2
        tp "primIntegerLog10" = PrimIntegerLog10

        tp "primIntegerEQ"  = PrimIntegerEQ
        tp "primIntegerLE"  = PrimIntegerLE
        tp "primIntegerLT"  = PrimIntegerLT

        tp "primRealToString" = PrimRealToString
        tp "primIntegerToReal" = PrimIntegerToReal
        tp "primRealEQ"  = PrimRealEQ
        tp "primRealLE"  = PrimRealLE
        tp "primRealLT"  = PrimRealLT
        tp "primRealAdd"  = PrimRealAdd
        tp "primRealSub"  = PrimRealSub
        tp "primRealNeg"  = PrimRealNeg
        tp "primRealMul"  = PrimRealMul
        tp "primRealDiv"  = PrimRealDiv
        tp "primRealAbs"  = PrimRealAbs
        tp "primRealSignum" = PrimRealSignum
        tp "primRealExpE" = PrimRealExpE
        tp "primRealPow"  = PrimRealPow
        tp "primRealLogE" = PrimRealLogE
        tp "primRealLogBase" = PrimRealLogBase
        tp "primRealLog2" = PrimRealLog2
        tp "primRealLog10" = PrimRealLog10
        tp "primRealToBits" = PrimRealToBits
        tp "primBitsToReal" = PrimBitsToReal
        tp "primRealSin"    = PrimRealSin
        tp "primRealCos"    = PrimRealCos
        tp "primRealTan"    = PrimRealTan
        tp "primRealSinH"   = PrimRealSinH
        tp "primRealCosH"   = PrimRealCosH
        tp "primRealTanH"   = PrimRealTanH
        tp "primRealASin"   = PrimRealASin
        tp "primRealACos"   = PrimRealACos
        tp "primRealATan"   = PrimRealATan
        tp "primRealASinH"  = PrimRealASinH
        tp "primRealACosH"  = PrimRealACosH
        tp "primRealATanH"  = PrimRealATanH
        tp "primRealATan2"  = PrimRealATan2
        tp "primRealSqrt"   = PrimRealSqrt
        tp "primRealTrunc"  = PrimRealTrunc
        tp "primRealCeil"   = PrimRealCeil
        tp "primRealFloor"  = PrimRealFloor
        tp "primRealRound"  = PrimRealRound
        tp "primSplitReal"  = PrimSplitReal
        tp "primDecodeReal" = PrimDecodeReal
        tp "primRealToDigits" = PrimRealToDigits
        tp "primRealIsInfinite" = PrimRealIsInfinite
        tp "primRealIsNegativeZero" = PrimRealIsNegativeZero

        tp "primUninitialized" = PrimUninitialized
        tp "primMakeRawUninitialized" = PrimRawUninitialized
        tp "primMarkArrayUninitialized" = PrimMarkArrayUninitialized
        -- the same primitive is used to implement both of these
        tp "primMarkArrayInitialized" = PrimMarkArrayInitialized
        tp "primMarkBitArrayInitialized" = PrimMarkArrayInitialized
        tp "primUninitBitArray" = PrimUninitBitArray
        tp "primIsBitArray" = PrimIsBitArray
        tp "primUpdateBitArray" = PrimUpdateBitArray
        tp "primBuildUndefined" = PrimBuildUndefined
        tp "primMakeRawUndefined" = PrimRawUndefined
        tp "primIsRawUndefined" = PrimIsRawUndefined
        tp "primImpCondOf" = PrimImpCondOf
        tp "primArrayNew" = PrimArrayNew
        tp "primArrayLength" = PrimArrayLength
        tp "primArraySelect" = PrimArraySelect
        tp "primArrayUpdate" = PrimArrayUpdate
        tp "primArrayDynSelect" = PrimArrayDynSelect
        tp "primArrayDynUpdate" = PrimArrayDynUpdate
        tp "primBuildArray" = PrimBuildArray

        tp "primSetSelPosition" = PrimSetSelPosition
        tp s = internalError ("unknown primitive: " ++ s ++ " " ++ prPosition (getIdPosition i))

instance PPrint PrimOp where
    pPrint d p op = text (toString op)

toString :: PrimOp -> String
toString PrimAdd = "+"
toString PrimSub = "-"
toString PrimAnd = "&"
toString PrimOr = "|"
toString PrimXor = "^"
toString PrimMul = "*"
toString PrimQuot = "/"
toString PrimRem = "%"
toString PrimSL = "<<"
toString PrimSRL = ">>"
toString PrimSRA = ">>>"
toString PrimInv = "~"
toString PrimNeg = "-"
toString PrimEQ = "=="
toString PrimEQ3 = "==="
toString PrimULE = "<="
toString PrimULT = "<"
toString PrimSLE = ".<="
toString PrimSLT = ".<"
toString PrimSignExt = "sext"
toString PrimZeroExt = "zext"
toString PrimTrunc = "trunc"
toString PrimExtract = "extract"
toString PrimConcat = "++"
toString PrimSplit = "split"
toString PrimBNot = "!"
toString PrimBAnd = "&&"
toString PrimBOr = "||"
toString PrimInoutCast = "primInoutCast"
toString PrimInoutUncast = "primInoutUncast"
toString PrimIf = "_if_"
toString PrimSelect = "select"
toString PrimValueOf = "valueOf"
toString PrimStringOf = "stringOf"
toString PrimOrd = "ord"
toString PrimChr = "chr"
toString PrimError = "_error"
toString PrimCurrentClock = "primCurrentClock"
toString p = show p

-- to name of wide-data operations
toWString :: PrimOp -> String
toWString PrimAdd = "add"
toWString PrimSub = "sub"
toWString PrimAnd = "and"
toWString PrimOr = "or"
toWString PrimXor = "xor"
toWString PrimMul = "mul"
toWString PrimQuot = "quot"
toWString PrimRem = "rem"
toWString PrimSL = "sl"
toWString PrimSRL = "srl"
toWString PrimSRA = "sra"
toWString PrimInv = "inv"
toWString PrimNeg = "neg"
toWString PrimEQ = "eq"
toWString PrimULE = "ule"
toWString PrimULT = "ult"
toWString PrimSLE = "sle"
toWString PrimSLT = "slt"
toWString PrimSignExt = "sext"
toWString PrimZeroExt = "zext"
toWString PrimTrunc = "trunc"
toWString PrimExtract = "extract"
toWString PrimConcat = "concat"
toWString PrimSplit = "split"
toWString PrimBNot = "bnot"
toWString PrimBAnd = "band"
toWString PrimBOr = "bor"
toWString PrimIf = "_if_"
toWString PrimSelect = "select"
toWString PrimValueOf = "valueOf"
toWString PrimStringOf = "stringOf"
toWString PrimOrd = "ord"
toWString PrimChr = "chr"
toWString PrimError = "_error"
toWString PrimCurrentClock = "primCurrentClock"
toWString p = show p

instance NFData PrimOp where
    rnf x = seq x ()

-----

-- For writing and readin PrimOp to a file

writePrimOp :: PrimOp -> Int
writePrimOp p = fromEnum p

readPrimOp :: Int -> PrimOp
readPrimOp n = toEnum n

-- -------------------------------------------------------------------
-- Routines for evaluating prim ops with constant arguments

-- shorthand notation
ans :: a -> Maybe (Either ErrMsg a)
ans x = Just $ Right x

err :: ErrMsg -> Maybe (Either ErrMsg a)
err msg = Just $ Left msg

no_answer :: Maybe a
no_answer = Nothing  -- XXX shouldn't these really be errors?
                     -- XXX See discussion of doPrimOp in IPrims.hs


-- ----
-- Data type for mixing argument types

data PrimArg = I Integer
             | D Double
             deriving (Eq)

instance PPrint PrimArg where
    pPrint d p (I i) = pparen (p > 0) $ text "I" <+> pPrint d 0 i
    pPrint d p (D r) = pparen (p > 0) $ text "D" <+> pPrint d 0 r

-- ----
-- Primitives returning Integer
evalPrimToInt :: PrimOp -> [Integer] -> [PrimArg] ->
                 Maybe (Either ErrMsg Integer)

-- basic math on sized values
evalPrimToInt PrimAdd  [s]     [I i1, I i2] = ans $ mask s (i1+i2)
evalPrimToInt PrimSub  [s]     [I i1, I i2] = ans $ mask s (i1-i2)
evalPrimToInt PrimMul  [_,_,s] [I i1, I i2] = ans $ mask s (i1*i2)
evalPrimToInt PrimQuot [s,_]   [I i1, I i2] =
    if (i2 == 0)
    then err EDivideByZero
    else ans $ mask s (i1 `quot` i2)
evalPrimToInt PrimRem  [_,s]   [I i1, I i2] =
    if (i2 == 0)
    then err EDivideByZero
    else ans $ mask s (i1 `rem` i2)
evalPrimToInt PrimNeg  [s]     [I i1]    = ans $ mask s (-i1)

-- bit-wise operators on sized values
evalPrimToInt PrimAnd [s] [I i1, I i2] = ans $ i1 `integerAnd` i2
evalPrimToInt PrimOr  [s] [I i1, I i2] = ans $ i1 `integerOr`  i2
evalPrimToInt PrimXor [s] [I i1, I i2] = ans $ i1 `integerXor` i2
evalPrimToInt PrimInv [s] [I i1]       = ans $ mask s (integerInvert i1)

-- shifting on sized values
evalPrimToInt PrimSL  [s,_] [I x, I sh]  =
    if (sh >= s)
    then ans 0
    else if (sh >= 0)
         then ans $ mask s (x * (2^sh))
         else no_answer
evalPrimToInt PrimSRL [s,_] [I x, I sh]  =
    if (sh >= s)
    then ans 0
    else if (sh >= 0)
         then ans $ x `div` (2^sh)
         else no_answer
evalPrimToInt PrimSRA [s,_] [I x, I sh]  =
    if (sh >= s)
    then -- this behavior, i.e., 0 if you shift too much,
         -- is intended to emulate what verilog simulators
         -- do.  iverilog and ncverilog have this behavior
         ans 0
    else if (sh >= 0)
         then evalPrimToInt PrimSignExt [sh, s-sh, s] [I (x `div` (2^sh))]
         else no_answer

-- extension and truncation on sized values
evalPrimToInt PrimZeroExt [_,_,_]   [I i] = ans i
evalPrimToInt PrimSignExt [_,s1,s2] [I i] =
    if (s1 >= 1 && s2 >= 0)  -- _ + s1 = s2
    then ans $ if i >= 2^(s1-1) then 2^s2 - 2^s1 + i else i
    else no_answer
evalPrimToInt PrimTrunc   [_,s,_]   [I i] = ans $ mask s i

-- extraction, concatenation and range-checking on sized values
evalPrimToInt PrimRange [s] [I lo, I hi, I x] =
    if x < lo || x > hi then
        internalError ("evalPrimToInt: PrimRange " ++ ppReadable (lo,hi,x))
    else
        ans $ x
evalPrimToInt PrimExtract [n,_,m] [I e, I h, I l] =
    if (h-l+1 < 0)
    then internalError
             ("evalPrimToInt: PrimExtract extract negative number of bits "
              ++ ppReadable ((n,m),(h,l,e)))
    else if (l >= 0)
         then ans $ mask m (integerSelect (h-l+1) l e)
         else no_answer
evalPrimToInt PrimConcat [s1,s2,s3] [I i1, I i2] =
    if (s2 >= 0)
    then ans $ i1 * 2^s2 + i2
    else no_answer
evalPrimToInt PrimSelect [k,m,_]    [I i] =
    if (m >= 0)
    then ans $ integerSelect k m i
    else no_answer
-- evalPrimToInt PrimSplit _ _ =

-- math on unbounded Integers
evalPrimToInt PrimIntegerAdd  _ [I i1, I i2] = ans $ i1 + i2
evalPrimToInt PrimIntegerSub  _ [I i1, I i2] = ans $ i1 - i2
evalPrimToInt PrimIntegerNeg  _ [I i1]       = ans $ (-i1)
evalPrimToInt PrimIntegerMul  _ [I i1, I i2] = ans $ i1 * i2
evalPrimToInt PrimIntegerDiv  _ [I i1, I i2] =
    if (i2 == 0)
    then err EDivideByZero
    else ans $ i1 `div` i2
evalPrimToInt PrimIntegerMod  _ [I i1, I i2] =
    if (i2 == 0)
    then err EDivideByZero
    else ans $ i1 `mod` i2
evalPrimToInt PrimIntegerQuot _ [I i1, I i2] =
    if (i2 == 0)
    then err EDivideByZero
    else ans $ i1 `quot` i2
evalPrimToInt PrimIntegerRem  _ [I i1, I i2] =
    if (i2 == 0)
    then err EDivideByZero
    else ans $ i1 `rem` i2
evalPrimToInt PrimIntegerExp  _ [I i1, I i2] =
    if (i2 < 0)
    then err EIntegerNegativeExponent
    else ans $ i1 ^ i2
evalPrimToInt PrimIntegerLog2 _ [I i1]       =
    if (i1 <= 0)
    then err EInvalidLog
    else ans $ log2 i1
evalPrimToInt PrimIntegerLog10 _ [I i1]      =
    if (i1 <= 0)
    then err EInvalidLog
    else ans $ log10 i1

-- conversions from unbounded to sized and vice-versa
evalPrimToInt PrimIntegerToBit [s] [I i] =
    if (i < 2^s && i > -(2^s))
    then ans $ mask s i
    else no_answer
evalPrimToInt PrimBitToInteger _   [I i] = ans i

-- conditional
evalPrimToInt PrimIf [s] [I i1, I i2, I i3] =
    ans $ if (i1 == 1) then i2 else i3

-- conversion to bits
evalPrimToInt PrimRealToBits _ [D d1] =
    ans $ toInteger (doubleToWord64 d1)

-- rounding, truncation, etc.
evalPrimToInt PrimRealTrunc _ [D d1] = ans $ truncate d1
evalPrimToInt PrimRealCeil  _ [D d1] = ans $ ceiling d1
evalPrimToInt PrimRealFloor _ [D d1] = ans $ floor d1
evalPrimToInt PrimRealRound _ [D d1] = ans $ round d1

-- all other prim ops are unhandled
evalPrimToInt _ _ _ = no_answer


-- ----
-- Primitives returning Bool
evalPrimToBool :: PrimOp -> [Integer] -> [PrimArg] ->
                  Maybe (Either ErrMsg Bool)

-- relational operators on sized values
evalPrimToBool PrimEQ  [s] [I i1, I i2] = ans $ i1 == i2
evalPrimToBool PrimEQ3 [s] [I i1, I i2] = ans $ i1 == i2
evalPrimToBool PrimULE [s] [I i1, I i2] = ans $ i1 <= i2
evalPrimToBool PrimULT [s] [I i1, I i2] = ans $ i1 <  i2
evalPrimToBool PrimSLE [s] [I i1, I i2] = ans $ (ext s i1) <= (ext s i2)
evalPrimToBool PrimSLT [s] [I i1, I i2] = ans $ (ext s i1) <  (ext s i2)

-- boolean logic
evalPrimToBool PrimBNot      _ [I i]        = ans $ i == 0
evalPrimToBool PrimBAnd      _ [I i1, I i2] = ans $ (i1 == 1) && (i2 == 1)
evalPrimToBool PrimBOr       _ [I i1, I i2] = ans $ (i1 == 1) || (i2 == 1)

-- relational operators on unbounded Integers
evalPrimToBool PrimIntegerEQ _ [I i1, I i2] = ans $ i1 == i2
evalPrimToBool PrimIntegerLE _ [I i1, I i2] = ans $ i1 <= i2
evalPrimToBool PrimIntegerLT _ [I i1, I i2] = ans $ i1 <  i2

-- relational operators
evalPrimToBool PrimRealEQ _ [D d1, D d2] = ans $ d1 == d2
evalPrimToBool PrimRealLE _ [D d1, D d2] = ans $ d1 <= d2
evalPrimToBool PrimRealLT _ [D d1, D d2] = ans $ d1 <  d2

-- property tests
evalPrimToBool PrimRealIsInfinite     _ [D d1] = ans $ isInfinite d1
evalPrimToBool PrimRealIsNegativeZero _ [D d1] = ans $ isNegativeZero d1

-- all other prim ops are unhandled
evalPrimToBool _ _ _ = no_answer


-- ----
-- Primitives returning Double
evalPrimToDouble :: PrimOp -> [Integer] -> [PrimArg] ->
                    Maybe (Either ErrMsg Double)

evalPrimToDouble PrimIntegerToReal _ [I i1] = ans $ fromInteger i1
evalPrimToDouble PrimBitsToReal    _ [I i1] =
    let d = word64ToDouble (fromInteger i1)
    in  if (isNaN d) then err EFloatNaN else ans d

-- basic math operators
evalPrimToDouble PrimRealAdd _ [D d1, D d2] =
    if ( (isPosInfinite d1 && isNegInfinite d2) ||
         (isNegInfinite d1 && isPosInfinite d2) )
    then err EAddPosAndNegInfinity
    else ans $ d1 + d2
evalPrimToDouble PrimRealSub _ [D d1, D d2] =
    if ( (isPosInfinite d1 && isPosInfinite d2) ||
         (isNegInfinite d1 && isNegInfinite d2) )
    then err EAddPosAndNegInfinity
    else ans $ d1 - d2
evalPrimToDouble PrimRealNeg _ [D d1] = ans (-d1)
evalPrimToDouble PrimRealMul _ [D d1, D d2] =
    if ( (isInfinite d1 && (d2 == 0.0)) ||
         (isInfinite d2 && (d1 == 0.0)) )
    then err EMultiplyZeroAndInfinity
    else ans $ d1 * d2
evalPrimToDouble PrimRealDiv _ [D d1, D d2] =
    if (d2 == 0.0)
    then err EDivideByZero
    else ans $ d1 / d2
evalPrimToDouble PrimRealAbs    _ [D d1] = ans (abs d1)
evalPrimToDouble PrimRealSignum _ [D d1] = ans (signum d1)

-- exponents and logarithms
evalPrimToDouble PrimRealExpE _ [D d1] = ans $ exp d1
evalPrimToDouble PrimRealPow  _ [D d1, D d2] = ans $ d1 ** d2
evalPrimToDouble PrimRealLogE _ [D d1] =
    if (d1 <= 0)
    then err EInvalidLog
    else  ans $ log d1
evalPrimToDouble PrimRealLogBase _ [D d1, D d2] =
    if (d2 <= 0)
    then err EInvalidLog
    else if (d1 <= 0)
    then err EInvalidLogBase
    else if ((d1 == 1) && (d2 == 1))
    then err EInvalidLogOneOne
    else ans $ logBase d1 d2
evalPrimToDouble PrimRealLog2 _ [D d1] =
    if (d1 <= 0)
    then err EInvalidLog
    else ans $ R.log2 d1
evalPrimToDouble PrimRealLog10 _ [D d1] =
    if (d1 <= 0)
    then err EInvalidLog
    else ans $ R.log10 d1
evalPrimToDouble PrimRealSqrt _ [D d1] =
    if (d1 < 0)
    then err ENegativeSqrt
    else ans $ sqrt d1

-- trig functions
evalPrimToDouble PrimRealSin   _ [D d1] = ans $ sin d1
evalPrimToDouble PrimRealCos   _ [D d1] = ans $ cos d1
evalPrimToDouble PrimRealTan   _ [D d1] = ans $ tan d1
evalPrimToDouble PrimRealSinH  _ [D d1] = ans $ sinh d1
evalPrimToDouble PrimRealCosH  _ [D d1] = ans $ cosh d1
evalPrimToDouble PrimRealTanH  _ [D d1] = ans $ tanh d1
evalPrimToDouble PrimRealASin  _ [D d1] = ans $ asin d1
evalPrimToDouble PrimRealACos  _ [D d1] = ans $ acos d1
evalPrimToDouble PrimRealATan  _ [D d1] = ans $ atan d1
evalPrimToDouble PrimRealASinH _ [D d1] = ans $ asinh d1
evalPrimToDouble PrimRealACosH _ [D d1] = ans $ acosh d1
evalPrimToDouble PrimRealATanH _ [D d1] = ans $ atanh d1
evalPrimToDouble PrimRealATan2 _ [D d1, D d2] = ans $ atan2 d1 d2

-- all other prim ops are unhandled
evalPrimToDouble _ _ _ = no_answer


-- ----
-- Double to String primitives
evalPrimToString :: PrimOp -> [Integer] -> [PrimArg] ->
                    Maybe (Either ErrMsg String)

-- XXX PrimIntegerToString could go here, but it needs access to the base
-- XXX (which we could add to PrimArg)
evalPrimToString PrimRealToString _ [D d1] = ans $ show d1

-- all other prim ops on Doubles are unhandled
evalPrimToString _ _ _ = no_answer


-- ----
-- Primitives returning (Integer, Double)
evalPrimToIntDouble :: PrimOp -> [Integer] -> [PrimArg] ->
                       Maybe (Either ErrMsg (Integer,Double))

evalPrimToIntDouble PrimSplitReal _ [D d1] = ans $ properFraction d1

-- all other prim ops are unhandled
evalPrimToIntDouble _ _ _ = no_answer


-- ----
-- Primitives returning (Bool, Integer, Integer)
evalPrimToBoolIntInt :: PrimOp -> [Integer] -> [PrimArg] ->
                        Maybe (Either ErrMsg (Bool,Integer,Integer))

evalPrimToBoolIntInt PrimDecodeReal _ [D d1] =
    let (mantissa, exponent) = decodeFloat d1
        -- include positive zero
        is_pos = (d1 >= 0) && not (isNegativeZero d1)
    in  ans (is_pos, mantissa, (toInteger exponent))

-- all other prim ops are unhandled
evalPrimToBoolIntInt _ _ _ = no_answer


-- ----
-- Primitives returning ([Integer], Integer)
evalPrimToListIntInt :: PrimOp -> [Integer] -> [PrimArg] ->
                        Maybe (Either ErrMsg ([Integer], Integer))

evalPrimToListIntInt PrimRealToDigits _ [I i, D d] =
    let -- "floatToDigits" only works for non-negative values
        (digits, exponent) = floatToDigits i (abs d)
    in  ans (map toInteger digits, toInteger exponent)

-- all other prim ops are unhandled
evalPrimToListIntInt _ _ _ = no_answer


-- -------------------------------------------------------------------
-- Typeclass to simplify evaluation of prim ops

class PrimResult a where
  primResult :: PrimOp -> [Integer] -> [PrimArg] -> Maybe (Either ErrMsg a)
  -- default implementation is to return no_answer for everything
  primResult _ _ _ = no_answer

instance PrimResult Bool where
  primResult op ts vs = evalPrimToBool op ts vs

instance PrimResult Integer where
  primResult op ts vs = evalPrimToInt op ts vs

instance PrimResult Double where
  primResult op ts vs = evalPrimToDouble op ts vs

instance PrimResult String where
  primResult op ts vs = evalPrimToString op ts vs

instance PrimResult (Integer, Double) where
  primResult op ts vs = evalPrimToIntDouble op ts vs

instance PrimResult (Bool, Integer, Integer) where
  primResult op ts vs = evalPrimToBoolIntInt op ts vs

instance PrimResult ([Integer], Integer) where
  primResult op ts vs = evalPrimToListIntInt op ts vs
