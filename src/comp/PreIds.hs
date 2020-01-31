module PreIds where
import Position
import PreStrings
import Id
import FStringCompat(FString)


-- identifier without a position
mk_no :: FString -> Id
mk_no fs = mkId noPosition fs

-- identifier in the Standard Prelude, with a position
prelude_id :: Position -> FString -> Id
prelude_id p fs = mkQId p fsPrelude fs

-- identifier in the Standard Prelude, with no position
prelude_id_no :: FString -> Id
prelude_id_no fs = prelude_id noPosition fs

-- identifier in the Standard Prelude, with a position
prelude_bsv_id :: Position -> FString -> Id
prelude_bsv_id p fs = mkQId p fsPreludeBSV fs

-- identifier in the Standard Prelude, with no position
prelude_bsv_id_no :: FString -> Id
prelude_bsv_id_no fs = prelude_bsv_id noPosition fs

-- add id properties to an already existing identifier
prop_prelude_id_no :: FString -> [IdProp] -> Id
prop_prelude_id_no fs props =
    addIdProps (prelude_id (updatePosStdlib noPosition True) fs) props

idB = prelude_id_no fsB
idR = prelude_id_no fsR
idArrow p = prelude_id p fsRArrow
idPrimUnit = prelude_id_no fsPrimUnit
idBit  = prelude_id_no fsBit
idInt  = prelude_id_no fsInt
idUInt = prelude_id_no fsUInt
idVReg = prelude_id_no fsVReg
idReg = prelude_id_no fsReg
idRWire = prelude_bsv_id_no fsRWire
idPulseWire = prelude_bsv_id_no fsPulseWire
idFIFO = mkQId noPosition fsFIFO fsFIFO
idFIFOF = mkQId noPosition fsFIFOF fsFIFOF
idSend = prelude_bsv_id_no fsSend
id_notFull = mk_no fsFIFO_notFull
id_notEmpty = mk_no fsFIFO_notEmpty
idEnq = mk_no fsFIFOEnq
idDeq = mk_no fsFIFODeq
idFirst = mk_no fsFIFOFirst
idInteger = prelude_id_no fsInteger
idReal = prelude_id_no fsReal
idRealAt pos = prelude_id pos fsReal
idString = prelude_id_no fsString
idChar = prelude_id_no fsChar
idHandle = prelude_id_no fsHandle
idBufferMode = prelude_id_no fsBufferMode
idNoBuffering = prelude_id_no fsNoBuffering
idLineBuffering = prelude_id_no fsLineBuffering
idBlockBuffering = prelude_id_no fsBlockBuffering
idFmt = prelude_id_no fsFmt
idPrimFmtConcat = prelude_id_no fsPrimFmtConcat
idPrimPriMux = prelude_id_no fsPrimPriMux
idFormat = prelude_id_no fsFormat
idFShow = prelude_id_no fsFShow
idfshow = prelude_id_no fsfshow
idBool = prelude_id_no fsBool
idPrimFst = prelude_id_no fsPrimFst
idPrimSnd = prelude_id_no fsPrimSnd
idPrimPair = prelude_id_no fsPrimPair
idFalse = prelude_id_no fsFalse
idTrue = prelude_id_no fsTrue
idSizeOf = prelude_id_no fsSizeOf
idTAdd = prelude_id_no fsTAdd
idTSub = prelude_id_no fsTSub
idTMul = prelude_id_no fsTMul
idTDiv = prelude_id_no fsTDiv
idTLog = prelude_id_no fsTLog
idTExp = prelude_id_no fsTExp
idTMax = prelude_id_no fsTMax
idTMin = prelude_id_no fsTMin
idAction = prelude_id_no fsAction
idPrimAction = prelude_id_no fsPrimAction
idToPrimAction = prelude_id_no fsToPrimAction
idFromPrimAction = prelude_id_no fsFromPrimAction
idFromActionValue_ = prelude_id_no fsFromActionValue_
idToActionValue_ = prelude_id_no fsToActionValue_
idRules = prelude_id_no fsRules
idSchedPragma = prelude_id_no fsSchedPragma
idValueOf = prelude_id_no fsPrimValueOf
idPrimIndex = prelude_id_no fsPrimIndex
idPrimSelectable = prelude_id_no fsPrimSelectable
idPrimUpdateable = prelude_id_no fsPrimUpdateable
idPrimWriteable = prelude_id_no fsPrimWriteable
idChangeSpecialWires pos = prelude_id pos fsChangeSpecialWires
idPrimSetSelPosition = prelude_id_no fsPrimSetSelPosition
idMaybe = prelude_id_no fsMaybe
idInvalid = prelude_id_no fsInvalid
idValid = prelude_id_no fsValid
idEmpty = prelude_id_no fsEmptyIfc
idFile = prelude_id_no fsFile

idActionValue = prelude_id_no fsActionValue
-- field names for the ActionValue interface
idAVValue = prelude_id_no fsAVValue
idAVAction = prelude_id_no fsAVAction

idActionValue_ = prelude_id_no fsActionValue_
-- field names for the ActionValue_ interface
idAVValue_ = prelude_id_no fsAVValue_
idAVAction_ = prelude_id_no fsAVAction_

-- names of the special selector functions in the Prelude
id__value = prelude_id_no fs__value
id__action = prelude_id_no fs__action
id__value_at pos = prelude_id pos fs__value
id__action_at pos = prelude_id pos fs__action

idComma = mk_no fsComma
idPlus = mk_no fsPlus
idMinus = mk_no fsMinus
idPrelude = mk_no fsPrelude
idPreludeBSV = mk_no fsPreludeBSV

idPreludePlus = prelude_id_no fsPlus

-- Used by deriving
idEq = prelude_id_no fsEq
idBits = prelude_id_no fsBits
idLiteral = prelude_id_no fsLiteral
idRealLiteral = prelude_id_no fsRealLiteral
idSizedLiteral = prelude_id_no fsSizedLiteral
idStringLiteral = prelude_id_no fsStringLiteral
idPrimParam = prelude_id_no fsPrimParam
idPrimPort = prelude_id_no fsPrimPort
idBounded = prelude_id_no fsBounded
idClsDeepSeqCond = prelude_id_no fsClsDeepSeqCond
idPrimDeepSeqCond = prelude_id_no fsPrimDeepSeqCond
idPrimSeqCond = prelude_id_no fsPrimSeqCond
idUndefined = prelude_id_no fsUndefined
idEqual = prelude_id_no fsEqual
idNotEqual = prelude_id_no fsNotEqual
idPack = prelude_id_no fsPack
idUnpack = prelude_id_no fsUnpack
idFmap = prelude_id_no fsFmap
idMaxBound = prelude_id_no fsMaxBound
idMinBound = prelude_id_no fsMinBound
idBuildUndef = prelude_id_no fsBuildUndef
idMakeUndef = prelude_id_no fsMakeUndef
idRawUndef = prelude_id_no fsRawUndef
idAdd = prop_prelude_id_no fsAdd [IdPCommutativeTCon]
idMax = prop_prelude_id_no fsMax [IdPCommutativeTCon]
idMin = prop_prelude_id_no fsMin [IdPCommutativeTCon]
idLog = prelude_id_no fsLog
idMul = prop_prelude_id_no fsMul [IdPCommutativeTCon]
idDiv = prelude_id_no fsDiv
idNumEq = prop_prelude_id_no fsNumEq [IdPCommutativeTCon]
idAnd = prelude_id_no fsAnd
idNot = prelude_id_no fsNot
idPrimSplit = prelude_id_no fsPrimSplit
idPrimConcat = prelude_id_no fsPrimConcat
idPrimMul = prelude_id_no fsPrimMul
idPrimQuot = prelude_id_no fsPrimQuot
idPrimRem = prelude_id_no fsPrimRem
idPrimTrunc = prelude_id_no fsPrimTrunc
idPrimOrd = prelude_id_no fsPrimOrd
idPrimChr = prelude_id_no fsPrimChr
idLiftM = prelude_id_no fsLiftM
idPrimError = prelude_id_no fsPrimError

-- used by GenWrap for "polymorphic" modules
idLiftModule = prelude_id_no fsLiftModule

-- Used by desugaring
id_lam pos = mkId pos fs_lam
id_if pos = mkId pos fs_if
id_read pos = mkId pos fs_read
id_write pos = mkId pos fs_write
idPreludeRead = prelude_id_no fsRead
idPreludeWrite = prelude_id_no fsRegWrite
idAssign = mkId noPosition fsAssign
idExtract pos = prelude_id pos fsExtract
idFromInteger pos = prelude_id pos fsFromInteger
idFromReal pos = prelude_id pos fsFromReal
idFromSizedInteger pos = prelude_id pos fsFromSizedInteger
idFromString pos = prelude_id pos fsFromString
idPrimCharToString pos = prelude_id pos fsPrimCharToString
idPrimToParam pos = prelude_id pos fsPrimToParam
idPrimToPort pos = prelude_id pos fsPrimToPort
id_case pos = mkId pos fs_case
idBind pos = prelude_id pos fsBind
idBind_ pos = prelude_id pos fsBind_
idReturn pos = prelude_id pos fsReturn
idMonad pos = prelude_id pos fsMonad
idIsModule = prelude_id_no fsIsModule
idModule = prelude_id_no fsModule
idId = prelude_id_no fsId
idPrimModule pos = prelude_id pos fsPrimModule
idPrimStringConcat = prelude_id_no fsPrimStringConcat
idAddRules pos = prelude_id pos fsAddRules
idMkRegU pos = prelude_id pos fsMkRegU
idTheResult pos = addIdProp (mkId pos fsTheResult) IdPRenaming
idF pos = mkId pos fsF
idM pos = mkId pos fsM
idC pos = mkId pos fsC
idPrimSelectFn pos = mkId pos fsPrimSelectFn
idPrimUpdateFn pos = mkId pos fsPrimUpdateFn
idPrimWriteFn pos = mkId pos fsPrimWriteFn
idPrimUpdateRangeFn pos = prelude_id pos fsPrimUpdateRangeFn
idSAction pos = mkId pos fsSAction
idSActionValue pos = mkId pos fsSActionValue
idStmtify pos = mkId pos fsStmtify
idCallServer pos = mkId pos fsCallServer
idSIf1 pos    = mkId pos fsSIf1
idSIf2 pos    = mkId pos fsSIf2
idSAbtIf1 pos = mkId pos fsSAbtIf1
idSAbtIf2 pos = mkId pos fsSAbtIf2
idSRepeat pos = mkId pos fsSRepeat
idSWhile pos  = mkId pos fsSWhile
idSFor pos    = mkId pos fsSFor
idSSeq pos    = mkId pos fsSSeq
idSPar pos    = mkId pos fsSPar
idSLabel pos  = mkId pos fsSLabel
idSJump pos   = mkId pos fsSJump
idSNamed pos  = mkId pos fsSNamed
idS    pos    = mkId pos fsS
idStmt pos    = mkId pos fsStmt
idSBreak pos  = mkId pos fsSBreak
idSContinue pos = mkId pos fsSContinue
idSReturn   pos = mkId pos fsSReturn
idCons pos    = mkId pos fsCons
idConcat pos  = mkId pos fsConcat
idNil     pos = mkId pos fsNil
idNothing pos = mkId pos fsNothing
idSprime  pos = mkId pos fsSprime

-- used to prevent implicit read etc.
idAsIfc = prelude_id_no fsAsIfc
idAsReg = prelude_id_no fsAsReg

-- used to inject state names
idName = prelude_id_no fsName
idPrimGetName = prelude_id_no fsPrimGetName
idPrimGetNameAt pos  = prelude_id pos fsPrimGetName
idPrimGetParamName = prelude_id_no fsPrimGetParamName
idPrimGetParamNameAt pos  = prelude_id pos fsPrimGetParamName
idPrimJoinNamesAt pos = prelude_id pos fsPrimJoinNames
idPrimExtNameIdxAt pos = prelude_id pos fsPrimExtNameIdx
idSetStateNameAt pos = prelude_id pos fsSetStateName
idGetModuleName = prelude_id_no fsGetModuleName

-- used to force the monad in a "module" expression to be a module,
-- so that we fail fast for good error positions
idForceIsModuleAt pos = prelude_id pos fsForceIsModule

-- use for communicating positions for errors, warnings and messages
idPosition = prelude_id_no fsPosition
idNoPosition = prelude_id_no fsNoPosition
idPrimGetEvalPosition = prelude_id_no fsPrimGetEvalPosition

-- used to carry attributes
idAttributes = prelude_id_no fsAttributes
idSetStateAttribAt pos = prelude_id pos fsSetStateAttrib

idType = prelude_id_no fsType
idTypeOf = prelude_id_no fsTypeOf
idSavePortType = prelude_id_no fsSavePortType
idPrintType = prelude_id_no fsPrintType

-- abstract type for implicit conditions
idPred = prelude_id_no fsPred

-- Used by iConv
idPrimBAnd = prelude_id_no fsPrimBAnd
idPrimBOr = prelude_id_no fsPrimBOr
idPrimBNot = prelude_id_no fsPrimBNot
idPrimSL = prelude_id_no fsPrimSL
idPrimSRL = prelude_id_no fsPrimSRL
idPrimInv = prelude_id_no fsPrimInv
idPrimIf = prelude_id_no fsPrimIf
idPrimCase = prelude_id_no fsPrimCase
idPrimArrayDynSelect = prelude_id_no fsPrimArrayDynSelect
idPrimBuildArray = prelude_id_no fsPrimBuildArray
idPrimWhen = prelude_id_no fsPrimWhen
idPrimSelect = prelude_id_no fsPrimSelect
idPrimSelectAt pos = prelude_id pos fsPrimSelect
idPrimZeroExt = prelude_id_no fsPrimZeroExt
idPrimSignExt = prelude_id_no fsPrimSignExt
idPrimJoinRules = prelude_id_no fsPrimJoinRules
idPrimNoRules = prelude_id_no fsPrimNoRules
idPrimRule = prelude_id_no fsPrimRule
idPrimJoinActions = prelude_id_no fsPrimJoinActions
idPrimAddSchedPragmas = prelude_id_no fsPrimAddSchedPragmas
idPrimNoActions = prelude_id_no fsPrimNoActions
idPrimNoExpIf = prelude_id_no fsPrimNoExpIf
idPrimExpIf = prelude_id_no fsPrimExpIf
idPrimNosplitDeep = prelude_id_no fsPrimNosplitDeep
idPrimSplitDeep = prelude_id_no fsPrimSplitDeep
idSplitDeepAV = prelude_id_no fsSplitDeepAV
idNosplitDeepAV = prelude_id_no fsNosplitDeepAV
idPrimFix pos = prelude_id pos fsPrimFix
idMfix = prelude_id_no fsMfix
idStaticAssert = mk_no fsStaticAssert
idDynamicAssert = mk_no fsDynamicAssert
idContinuousAssert = mk_no fsContinuousAssert
id_staticAssert = mk_no  fs_staticAssert
id_dynamicAssert = mk_no fs_dynamicAssert
id_continuousAssert = mk_no fs_continuousAssert
idClsUninitialized = prelude_id_no fsClsUninitialized
idPrimUninitialized = prelude_id_no fsPrimUninitialized
idPrimUninitializedAt pos = prelude_id pos fsPrimUninitialized
idPrimMakeUninitialized = prelude_id_no fsPrimMakeUninitialized
idPrimRawUninitialized = prelude_id_no fsPrimRawUninitialized
idPrimPoisonedDef = prelude_id_no fsPrimPoisonedDef
idStringAt pos = prelude_id pos fsString
idFmtAt pos = prelude_id pos fsFmt
idPrimStringConcatAt pos = prelude_id pos fsPrimStringConcat

-- clock and reset identifiers
idClock = prelude_id_no fsClock
idClockOsc = prelude_id_no fsClockOsc
idClockGate = prelude_id_no fsClockGate
idReset = prelude_id_no fsReset
idInout  = prelude_id_no fsInout
idInout_ = prelude_id_no fsInout_
idPrimInoutCast = prelude_id_no fsPrimInoutCast
idPrimInoutUncast = prelude_id_no fsPrimInoutUncast
idPrimInoutCast0 = prelude_id_no fsPrimInoutCast0
idPrimInoutUncast0 = prelude_id_no fsPrimInoutUncast0

idExposeCurrentClock = prelude_id_no fsExposeCurrentClock
idExposeCurrentReset = prelude_id_no fsExposeCurrentReset

-- needed for noClock constant in ISyntax
idNoClock = prelude_id_no fsNoClock
-- needed for noReset constant in ISyntax
idNoReset = prelude_id_no fsNoReset
-- needed for GenWrap
idPrimReplaceClockGate = prelude_id_no fsPrimReplaceClockGate

idClk = mk_no fsClk -- position?
idRst = mk_no fsRst -- position?

idCLK = mk_no fsCLK
idCLK_GATE = mk_no fsCLK_GATE
-- idRSTN = mk_no fsRSTN

idDefaultClock = mk_no fsDefaultClock
idDefaultReset = mk_no fsDefaultReset

-- iConv junk
idPrimSplitFst = prelude_id_no fsPrimSplitFst
idPrimSplitSnd = prelude_id_no fsPrimSplitSnd

id_x   = setBadId $ mk_no fs_x
id_y   = setBadId $ mk_no fs_y
id_fun = setBadId $ mk_no fs_fun
id_forallb = setBadId $ mk_no fs_forallb

tmpVarIds = map (enumId "a" noPosition) [1000..]
tmpVarXIds = map (enumId "x" noPosition) [1000000..]
tmpVarYIds = map (enumId "y" noPosition) [2000000..]
tmpVarSIds = map (enumId "s" noPosition) [3000000..]
tmpTyNumIds = map (enumId "tnum" noPosition) [4000000..]
tmpTyVarIds = map (enumId "v" noPosition) [100..]

-- used by iExpand
idPrimEQ = prelude_id_no fsPrimEQ
idPrimULE = prelude_id_no fsPrimULE
idPrimULT = prelude_id_no fsPrimULT
idPrimSLE = prelude_id_no fsPrimSLE
idPrimSLT = prelude_id_no fsPrimSLT

-- used by iTransform
idPrimAdd = prelude_id_no fsPrimAdd
idPrimSub = prelude_id_no fsPrimSub

-- used by AddCFWire
idVRWireN   = prelude_bsv_id_no fsVRWireN
idVmkRWire1 = prelude_bsv_id_no fsVmkRWire1
idWGet = prelude_bsv_id_no fsWGet
idWSet = prelude_bsv_id_no fsWSet
idWHas = prelude_bsv_id_no fsWHas

-- versions parametrized on position
idPrimConcatAt pos = prelude_id pos fsPrimConcat
idTrueAt pos = prelude_id pos fsTrue
idAddRulesAt pos = prelude_id pos fsAddRules
idOrAt pos = prelude_id pos fsOr
idEqualAt pos = prelude_id pos fsEqual
idNotEqualAt pos = prelude_id pos fsNotEqual
idPrimUnitAt pos = prelude_id pos fsPrimUnit
idErrorAt pos = prelude_id pos fsError
idNegateAt pos = prelude_id pos fsNegate
idIdentityAt pos = prelude_id pos fsIdentity
idNotAt pos = prelude_id pos fsNot
idInvertAt pos = prelude_id pos fsInvert
idPercentAt pos = prelude_id pos fsPercent
idModuleAt pos = prelude_id pos fsModule
idIsModuleAt pos = prelude_id pos fsIsModule
idActionAt pos = prelude_id pos fsAction
idActionValueAt pos = prelude_id pos fsActionValue
idActionValue_At pos = prelude_id pos fsActionValue_
idIntAt pos = prelude_id pos fsInt
idUnpackAt pos = prelude_id pos fsUnpack
idStarAt pos = prelude_id pos fsStar
idSlashAt pos = prelude_id pos fsSlash
idStarStarAt pos = prelude_id pos fsStarStar
idPlusAt pos = prelude_id pos fsPlus
idMinusAt pos = prelude_id pos fsMinus
idLshAt pos = prelude_id pos fsLsh
idRshAt pos = prelude_id pos fsRsh
idLtAt pos = prelude_id pos fsLT
idGtAt pos = prelude_id pos fsGT
idLtEqAt pos = prelude_id pos fsLtEq
idGtEqAt pos = prelude_id pos fsGtEq
idAndAt pos = prelude_id pos fsAnd
idBitAndAt pos = prelude_id pos fsBitAnd
idBitOrAt pos = prelude_id pos fsBitOr
idCaretAt pos = prelude_id pos fsCaret
idTildeCaretAt pos = prelude_id pos fsTildeCaret
idCaretTildeAt pos = prelude_id pos fsCaretTilde
idReduceAndAt pos = prelude_id pos fsReduceAnd
idReduceOrAt pos = prelude_id pos fsReduceOr
idReduceXorAt pos = prelude_id pos fsReduceXor
idReduceNandAt pos = prelude_id pos fsReduceNand
idReduceNorAt pos = prelude_id pos fsReduceNor
idReduceXnorAt pos = prelude_id pos fsReduceXnor
idRulesAt pos = prelude_id pos fsRules
idConstAllBitsSetAt pos = prelude_id pos fsConstAllBitsSet
idConstAllBitsUnsetAt pos = prelude_id pos fsConstAllBitsUnset

-- list declaration desugaring
idListAt pos = prelude_id pos fsList

-- array declaration desugaring
idPrimArrayAt pos = prelude_id pos fsPrimArray
idPrimArrayNewAt pos = prelude_id pos fsPrimArrayNew
idPrimArrayNewUAt pos = prelude_id pos fsPrimArrayNewU
idPrimArrayLengthAt pos = prelude_id pos fsPrimArrayLength
idPrimArrayInitializeAt pos = prelude_id pos fsPrimArrayInitialize
idPrimArrayCheckAt pos = prelude_id pos fsPrimArrayCheck

-- list identifiers for catching type errors on lists
idList = prelude_id_no fsList  -- there is no List::List
idListN = mkQId noPosition fsListN fsListN  -- not yet moved to Prelude
idVector = mkQId noPosition fsVector fsVector  -- but renamed to Vector
idToVector = mkQId noPosition fsVector fsToVector
idToListN  = mkQId noPosition fsListN fsToListN
idPrimArray = prelude_id_no fsPrimArray

-- system task ids
idFinish    = prelude_id_no fsFinish
idStop      = prelude_id_no fsStop

idDisplay   = prelude_id_no fsDisplay
idDisplayh  = prelude_id_no fsDisplayh
idDisplayb  = prelude_id_no fsDisplayb
idDisplayo  = prelude_id_no fsDisplayo
idWrite     = prelude_id_no fsWrite
idWriteh    = prelude_id_no fsWriteh
idWriteb    = prelude_id_no fsWriteb
idWriteo    = prelude_id_no fsWriteo

idFDisplay   = prelude_id_no fsFDisplay
idFDisplayh  = prelude_id_no fsFDisplayh
idFDisplayb  = prelude_id_no fsFDisplayb
idFDisplayo  = prelude_id_no fsFDisplayo
idFWrite     = prelude_id_no fsFWrite
idFWriteh    = prelude_id_no fsFWriteh
idFWriteb    = prelude_id_no fsFWriteb
idFWriteo    = prelude_id_no fsFWriteo

idSWriteAV   = prelude_id_no fsSWriteAV
idSWrite     = prelude_id_no fsSWrite
idSWritehAV  = prelude_id_no fsSWritehAV
idSWriteh    = prelude_id_no fsSWriteh
idSWritebAV  = prelude_id_no fsSWritebAV
idSWriteb    = prelude_id_no fsSWriteb
idSWriteoAV  = prelude_id_no fsSWriteoAV
idSWriteo    = prelude_id_no fsSWriteo
idSFormatAV  = prelude_id_no fsSFormatAV
idSFormat    = prelude_id_no fsSFormat

idErrorTask  = prelude_id_no fsErrorTask
idWarnTask   = prelude_id_no fsWarnTask
idInfoTask   = prelude_id_no fsInfoTask
idFatalTask  = prelude_id_no fsFatalTask

idSVA        = prelude_id_no fsSVA
idSvaParam   = prelude_id_no fsSvaParam
idSvaBool    = prelude_id_no fsSvaBool
idSvaNumber  = prelude_id_no fsSvaNumber

idSVAsampled = prelude_id_no fsSVAsampled
idSVArose    = prelude_id_no fsSVArose
idSVAfell    = prelude_id_no fsSVAfell
idSVAstable  = prelude_id_no fsSVAstable
idSVApast    = prelude_id_no fsSVApast
idSVAonehot  = prelude_id_no fsSVAonehot
idSVAonehot0 = prelude_id_no fsSVAonehot0
idSVAisunknown = prelude_id_no fsSVAisunknown
idSVAcountones = prelude_id_no fsSVAcountones

idRandom     = prelude_id_no fsRandom

idDumpon    = prelude_id_no fsDumpon
idDumpoff   = prelude_id_no fsDumpoff
idDumpvars  = prelude_id_no fsDumpvars
idDumpall   = prelude_id_no fsDumpall
idDumplimit = prelude_id_no fsDumplimit
idDumpflush = prelude_id_no fsDumpflush
idDumpfile  = prelude_id_no fsDumpfile
idTime      = prelude_id_no fsTime
idSTime     = prelude_id_no fsSTime
idFOpen     = prelude_id_no fsFOpen
idFGetc     = prelude_id_no fsFGetc
idUngetc    = prelude_id_no fsUngetc
idFClose    = prelude_id_no fsFClose
idFFlush    = prelude_id_no fsFFlush
idTestPlusargs = prelude_id_no fsTestPlusargs
idRealToBits = prelude_id_no fsRealToBits
idBitsToReal = prelude_id_no fsBitsToReal

taskIds = [ idFinish, idStop,
            --
            idDisplay, idDisplayh, idDisplayb, idDisplayo,
            idWrite, idWriteb, idWriteh, idWriteo,
            --
            idErrorTask, idWarnTask, idInfoTask, idFatalTask,
            --
            idRandom,
            --
            idFDisplay, idFDisplayh, idFDisplayb, idFDisplayo,
            idFWrite, idFWriteb, idFWriteh, idFWriteo,
            --
            idSFormatAV, idSFormat,
            idSWriteAV, idSWrite, idSWritehAV, idSWriteh,
            idSWritebAV, idSWriteb, idSWriteoAV, idSWriteo,
            idFormat,
            --
	    idSVA,
            --
	    idDumpon,  idDumpoff, idDumpvars, idDumpflush, idDumpfile,
            idDumpall, idDumplimit,
            --
            idTime, idSTime,
            --
            idFOpen, idFGetc, idUngetc, idFClose, idFFlush,
            --
            idTestPlusargs
          ]

-- these are explicitly NOT supported in user code
-- they are for internal use only (so not part of the taskids list)
idSigned   pos = prelude_id pos fsSigned
idUnsigned pos = prelude_id pos fsUnsigned

-- classes hardcoded in the Prelude which were added for ContextErrors
idBitwise   = prelude_id_no fsBitwise
idBitReduce = prelude_id_no fsBitReduce
idBitExtend = prelude_id_no fsBitExtend
idArith     = prelude_id_no fsArith
idOrd       = prelude_id_no fsOrd

-- names used for tuple fields internally?
tupleIds = map (\fs -> mkId noPosition fs) fsTuples
-- names exposed to the BSV user
idTuple2 = prelude_id_no fsTuple2
idTuple3 = prelude_id_no fsTuple3
idTuple4 = prelude_id_no fsTuple4
idTuple5 = prelude_id_no fsTuple5
idTuple6 = prelude_id_no fsTuple6
idTuple7 = prelude_id_no fsTuple7
idTuple8 = prelude_id_no fsTuple8

requiredClasses = [idUndefined, idClsDeepSeqCond, idClsUninitialized]
