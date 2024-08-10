{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
-- This is used to guarantee that getErrorText covers all the cases
-- Note that the OPTIONS line must be first !!!!

module Error(
             -- internal errors
             internalError,

             -- initialize the error handler
             ErrorHandle, initErrorHandle, setErrorHandleFlags,

             -- update the error handler state when files are opened/closed
             recordHandleOpen, recordHandleClose, closeOpenHandles,

             -- errors, warnings, and messages
             ErrMsg(..),
             EMsg, WMsg,
             EMsgs(..),  -- a list of EMsg, to avoid overlapping instances
             bsWarningsAndErrors,
             bsError, bsErrorNoExit,
             bsErrorDemotable,
             bsWarning,
             bsMessage,
             -- version when not in the IO monad
             bsErrorUnsafe,
             -- versions that display a context following the message
             MsgContext, emptyContext,
             bsWarningsAndErrorsWithContext,
             bsErrorWithContext, bsErrorWithContextNoExit,
             bsErrorDemotableWithContext,
             bsWarningWithContext,

             -- exit after multiple (delayed) errors
             exitFail,
             -- exit without error (if the user requests early exit)
             exitOK,
             -- exit with the same code as a system call that failed
             exitFailWith,

             -- report errors in ExceptT [EMsg] IO
             convExceptTToIO,

             -- used for displaying messages as a string
             -- (in .ba file, in Verilog dynamic error, in Tcl)
             showErrorList, showWarningList,
             getErrMsgTag
            ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import ErrorUtil(internalError)

-- displaying messages
import Data.List(sortBy, intercalate, nub, delete, partition)
import Data.Char(toUpper)

import Util(quote, unwordsOr, unwordsAnd, itos, doubleQuote, fst3, fth4)
import IntegerUtil(integerFormat)
import Position
import PPrint
import Classic(isClassic)
import qualified Flags as F

-- error handling
import Data.List(genericLength)
import qualified Data.Set as S
import System.IO(Handle, hClose, hPutStr, stderr)
import System.Exit(exitWith, ExitCode(..))
import Control.Monad(when)
import Control.Monad.Except(ExceptT, runExceptT)
import qualified Control.Exception as CE
import Data.IORef
import System.IO.Unsafe(unsafePerformIO)


-- -------------------------
--
-- Usage:
--
-- There are two interfaces for signaling errors:
--
-- (1) The function internalError is for internal compiler errors,
--     such as when a compiler invariant is broken.  This function
--     can be called from anywhere, whether in the IO monad or not.
--     This function is defined in ErrorUtil to avoid cyclic importing.
--     (Primitive packages can import ErrorUtil if they only need the
--     internalError function.)
--
-- (2) For reporting of user errors, there are the functions
--     bsMessage, bsWarn, and bsError.  These are in the IO monad;
--     an unsafePerformIO version exists for non-IO callers.
--     These require an argument which is the ErrorState, that can
--     be initialized with initErrorState.
--
--     The bsError function exits; to emit an error and continue, use
--     the function bsErrorNoExit.  When ready to exit, use exitFail
--     (to signal failure).
--
--     When the system wants to exit normally, it must also inform the
--     error handler, so use the function exitOK.
--
--     All of these require an ErrorHandle argument.  The initial value
--     can be created with initErrorHandle.
--
-- In some places (the scheduler, bluetcl), we want to convert errors to
-- strings (for storing in the .ba file, or for reporting as a tcl error),
-- so some functions for this are exposed.
--
-- A PPrint instance exists for EMsg so that internal messages
-- (such as debug dumps or calls to internalError) can display EMsgs.
-- Do not use this for output intended for the user!
--

----

--
-- TODO:
--
--  * Finish conversion to Doc type from GHCPretty instead of String,
--    by changing any String fields in ErrMsg to be Doc if the text
--    needs to assert its own formatting.
--
--  * Make separate errors for EBadIfcType's various arguments
--
--  * Some modules use the Either type to return errors assume no warnings.
--    They could be upgraded to the ErrorMonad.
--

-- -------------------------

data ErrorState = ErrorState
        {
          -- any warnings that the user has asked to promote
          promotionSet :: MsgSet,
          -- any errors that the user has asked to demote
          demotionSet :: MsgSet,

          -- any warnings that the user has asked to suppress
          suppressionSet :: MsgSet,
          -- number of warnings that were suppressed
          suppressedCount :: Integer,

          -- we also store state that needs handling on exit:

          -- set of open handles, that need to be flushed/closed on exit
          openHandles :: [Handle]

        }

-- -----

data MsgSet = AllMsgs | SomeMsgs (S.Set String)

toMsgSet :: F.MsgListFlag -> MsgSet
toMsgSet (F.AllMsgs) = AllMsgs
toMsgSet (F.SomeMsgs msgs) = SomeMsgs (S.fromList msgs)

memberMsgSet :: String -> MsgSet -> Bool
memberMsgSet _ (AllMsgs) = True
memberMsgSet s (SomeMsgs msg_set) = S.member s msg_set

-- -------------------------

newtype ErrorHandle = ErrorHandle (IORef ErrorState)

-- takes the Flag values as arguments
initErrorHandle :: IO ErrorHandle
initErrorHandle = do
  let init_state = ErrorState {
                     promotionSet = SomeMsgs S.empty,
                     demotionSet = SomeMsgs S.empty,
                     suppressionSet = SomeMsgs S.empty,
                     suppressedCount = 0,
                     openHandles = []
                   }
  ref <- newIORef init_state
  return (ErrorHandle ref)

setErrorHandleFlags :: ErrorHandle -> F.Flags -> IO ()
setErrorHandleFlags ref flags = do
  state <- readErrorState ref
  let new_state = state {
                    promotionSet = toMsgSet (F.promoteWarnings flags),
                    demotionSet = toMsgSet (F.demoteErrors flags),
                    suppressionSet = toMsgSet (F.suppressWarnings flags)
                  }
  writeErrorState ref new_state

readErrorState :: ErrorHandle -> IO ErrorState
readErrorState (ErrorHandle ref) = readIORef ref

writeErrorState :: ErrorHandle -> ErrorState -> IO ()
writeErrorState (ErrorHandle ref) new_state = writeIORef ref new_state

-- -------------------------

serror :: String
serror = "error"
swarning :: String
swarning = "warning"
smessage :: String
smessage = "message"


emptyContext :: Doc
emptyContext = empty

-- -----

-- Separate calls to bsWarning, bsDemotableError, and bsError
-- runs the risk of exiting before displaying all messages.
-- Having one function allows us to report everything.
-- (And we can sort all the messages together by position etc.)
--
bsWarningsAndErrors :: ErrorHandle -> [EMsg] -> [EMsg] -> [EMsg] -> IO ()
bsWarningsAndErrors ref ws ds es =
    bsWarningsAndErrorsWithContext ref emptyContext ws ds es

bsWarningsAndErrorsWithContext :: ErrorHandle -> MsgContext ->
                                  [EMsg] -> [EMsg] -> [EMsg] -> IO ()
bsWarningsAndErrorsWithContext ref ctx [] [] [] = do
    internalError ("bsWarningsAndErrors called with null list")
bsWarningsAndErrorsWithContext ref ctx ws ds es = do
  state0 <- readErrorState ref
  -- warn if the user requested to demote non-demotable errors
  let isDemoted t = memberMsgSet t (demotionSet state0)
      bad_tags = filter isDemoted (map (getErrMsgTag . snd) es)
      nondem_wmsg = (cmdPosition, WNonDemotableErrors bad_tags)
      -- allow the warning to be suppressed
      ws' = if (null bad_tags)
            then ws
            else (nondem_wmsg:ws)
  -- suppress warnings and demote demotable errors
  let (state1, warn_ws, err_ws) = handleWarnings state0 ctx ws'
      (state2, warn_ds, err_ds) = handleDemotableErrors state1 ctx ds
  -- write back the state first, because "doPreExitActions" may read it
  writeErrorState ref state2
  let final_warns = warn_ws ++ warn_ds
      final_errs = err_ws ++ err_ds ++ es
  -- issue warnings
  when (not (null final_warns)) $ do
      -- the show*List function will sort the messages
      -- XXX should we indicate which are demoted errors?
      hPutStr stderr (showWarningListWithContext ctx final_warns)
  -- issue errors
  when (not (null final_errs)) $ do
      doPreExitActions ref
      -- use exceptions, so that bluetcl can handle the error
      -- the show*List function will sort the messages
      -- XXX should we indicate which are promoted warnings?
      CE.throw $ CE.ErrorCall (showErrorListWithContext ctx final_errs)

handleDemotableErrors :: ErrorState -> MsgContext -> [EMsg] ->
                         (ErrorState, [WMsg], [EMsg])
handleDemotableErrors state ctx ds =
  let
      isDemoted t = memberMsgSet t (demotionSet state)
      (warn_ds, err_ds) = partition (isDemoted . getErrMsgTag . snd) ds
      -- once demoted to a warning, it can also be suppressed
      -- (a demoted error cannot be promoted, so we do not consult that set)
      (new_state, warn_ds') = suppressWarnings state warn_ds
  in
      (new_state, warn_ds', err_ds)

handleWarnings :: ErrorState -> MsgContext -> [WMsg] ->
                  (ErrorState, [WMsg], [EMsg])
handleWarnings state ctx ws =
    let
        -- the suppression list is consulted first
        (new_state, ws') = suppressWarnings state ws
        -- then, we check whether any can be promoted
        -- (but we exempt any that are also in the demote list)
        -- XXX note: promoting all and demoting all == no change
        isPromoted t = memberMsgSet t (promotionSet state) &&
                       not (memberMsgSet t (demotionSet state))
        (err_ws, warn_ws) = partition (isPromoted . getErrMsgTag . snd) ws'
    in
        (new_state, warn_ws, err_ws)

bsError :: ErrorHandle -> [EMsg] -> IO a
bsError ref es = do
  bsWarningsAndErrors ref [] [] es
  -- we know that the above call will always error;
  -- this line is to reflect that in the return type
  internalError ("bsError")

bsErrorWithContext :: ErrorHandle -> MsgContext -> [EMsg] -> IO a
bsErrorWithContext ref ctx es = do
  bsWarningsAndErrorsWithContext ref ctx [] [] es
  -- we know that the above call will always error;
  -- this line is to reflect that in the return type
  internalError ("bsErrorWithContext")

bsErrorDemotable :: ErrorHandle -> [EMsg] -> IO ()
bsErrorDemotable ref ds = bsWarningsAndErrors ref [] ds []

bsErrorDemotableWithContext :: ErrorHandle -> MsgContext -> [EMsg] -> IO ()
bsErrorDemotableWithContext ref ctx ds =
    bsWarningsAndErrorsWithContext ref ctx [] ds []

bsWarning :: ErrorHandle -> [EMsg] -> IO ()
bsWarning ref ws = bsWarningsAndErrors ref ws [] []

bsWarningWithContext :: ErrorHandle -> MsgContext -> [EMsg] -> IO ()
bsWarningWithContext ref ctx ws =
    bsWarningsAndErrorsWithContext ref ctx ws [] []


bsMessage :: ErrorHandle -> [EMsg] -> IO ()
bsMessage _ [] = internalError ("bsMessage called with null list")
bsMessage ref ms = do
  state <- readErrorState ref
  -- allow the user to suppress messages
  let (new_state, ms') = suppressWarnings state ms
  writeErrorState ref new_state
  when (not (null ms')) $
      hPutStr stderr (showMessageList ms')


bsErrorUnsafe :: ErrorHandle -> [EMsg] -> a
bsErrorUnsafe ref es = unsafePerformIO (bsError ref es)


suppressWarnings :: ErrorState -> [WMsg] -> (ErrorState, [WMsg])
suppressWarnings state ws =
  let notSuppressed t = not $ memberMsgSet t (suppressionSet state)
      ws' = filter (notSuppressed . getErrMsgTag . snd) ws
      num_suppressed :: Integer
      num_suppressed = genericLength ws - genericLength ws'
      old_count = suppressedCount state
      new_count = old_count + num_suppressed
      new_state = state { suppressedCount = new_count }
  in  (new_state, ws')


getSuppressionWarning :: ErrorState -> [WMsg]
getSuppressionWarning state =
  case (suppressedCount state) of
    0 -> []
    n -> let wmsg = (noPosition, WSuppressedWarnings n)
         in  snd $ suppressWarnings state [wmsg]

reportSuppressionWarning :: ErrorHandle -> IO ()
reportSuppressionWarning ref = do
  state <- readErrorState ref
  case (getSuppressionWarning state) of
    [] -> return ()
    ws -> do hPutStr stderr (showWarningList ws)
             -- clear the list of warnings
             -- so that a later caller won't re-report them
             let new_state = state { suppressedCount = 0 }
             writeErrorState ref new_state


recordHandleOpen :: ErrorHandle -> Handle -> IO ()
recordHandleOpen ref hdl = do
  state <- readErrorState ref
  let new_state = state { openHandles = (hdl : (openHandles state)) }
  writeErrorState ref new_state

recordHandleClose :: ErrorHandle -> Handle -> IO ()
recordHandleClose ref hdl = do
  state <- readErrorState ref
  let new_state = state { openHandles = delete hdl (openHandles state) }
  writeErrorState ref new_state

closeOpenHandles :: ErrorHandle -> IO ()
closeOpenHandles ref = do
  state <- readErrorState ref
  mapM_ hClose (openHandles state)
  let new_state = state { openHandles = [] }
  writeErrorState ref new_state


-- actions to do before exit (success or failure)
doPreExitActions :: ErrorHandle -> IO ()
doPreExitActions ref = do
  -- close any open handles
  closeOpenHandles ref
  -- report a suppression warning, if necessary
  reportSuppressionWarning ref


-- -------------------------

bsErrorNoExit :: ErrorHandle -> [EMsg] -> IO ()
bsErrorNoExit ref es = bsErrorWithContextNoExit ref emptyContext es

bsErrorWithContextNoExit :: ErrorHandle -> MsgContext -> [EMsg] -> IO ()
bsErrorWithContextNoExit ref ctx es = do
  -- nothing needs to be updated in the state
  hPutStr stderr (showErrorListWithContext ctx es)

exitFail :: ErrorHandle -> IO a
exitFail ref = exitFailWith ref 1

exitFailWith :: ErrorHandle -> Int -> IO a
exitFailWith ref n = do
  doPreExitActions ref
  exitWith (ExitFailure n)

-- -------------------------

-- For exiting BSC prematurely (such as with -KILL or -E)
exitOK :: ErrorHandle -> IO a
exitOK ref = do
  doPreExitActions ref
  exitWith ExitSuccess

-- -------------------------

-- We can't use [EMsg] with ExceptT because it leads to overlapping
-- instance problems. Instead, we will wrap it with a newtype.
newtype EMsgs = EMsgs { errmsgs :: [EMsg] }

-- -------------------------

convExceptTToIO :: ErrorHandle -> ExceptT EMsgs IO a -> IO a
convExceptTToIO ref fn =
    do mres <- runExceptT fn
       case mres of
         Left msgs -> bsError ref (errmsgs msgs)
         Right res -> return res

-- -------------------------

--
-- Data Types
--

type MsgContext = Doc

type EMsg = (Position, ErrMsg)
type WMsg = EMsg

data ErrMsg =
        -- Lexer/parser error messages
          EBadCharLit
        | EBadStringLit
        | EBadLexChar Char
        | ECPPDirective                 -- ^ CPP directive found when not expected
        | EUntermComm Position
        | EMissingNL
        | EBadLineDirective             -- ^ bad `line directive
        | EBadSymbol String             -- ^ bad operator/symbol
        | EBadStringEscapeChar Char     -- ^ bad character follows \ in string
        | EStringNewline                -- ^ newline in string
        | EStringEOF                    -- ^ end of file inside string
        | ESyntax !String ![String]     -- ^ found token, expected tokens
        | EUnsupportedBitVector         -- ^ bit vectors [N:0] only
        | EUnsupportedNumReal String    -- ^ real numbers not supported
        | EUnsupportedNumUndetermined String -- ^ number with x's and z's
        | EUnsupportedPatAll1 String    -- ^ '1 not supported as pattern
        | EMixedLitInNonPatCase String  -- ^ ? not allowed in non-pattern case
        | EUnsupportedImport !String !String -- ^ package, identifier: only "foo::*" supported for imports
        | EMissingProvisoArgs !String   -- ^ missing proviso arguments for typeclass...

        | EAttribsTypedef   -- ^ attributes not allowed for typedef
        | EAttribsTypeclass -- ^ attributes not allowed for typeclass
        | EAttribsInstance  -- ^ attributes not allowed for instance
        | EAttribsVarDef    -- ^ attributes not allowed for variable definition
        | EAttribsIfcDecl   -- ^ attributes not allowed for interface declaration
        | EAttribsBeginEnd  -- ^ attributes not allowed for begin .. end
        | EAttribsAction    -- ^ attributes not allowed for begin .. end
        | EAttribsActionValue -- ^ attributes not allowed for begin .. end
        | EAttribsReturn    -- ^ attributes not allowed for "return"
        | EAttribsIf        -- ^ attributes not allowed for if-statement
        | EAttribsFor       -- ^ attributes not allowed for for-statement
        | EAttribsWhile     -- ^ attributes not allowed for while-statement
        | EAttribsRepeat    -- ^ attributes not allowed for repeat-statement
        | EAttribsBreak     -- ^ attributes not allowed for break-statement
        | EAttribsExpr !String
        | EInvalidMethod -- ^ not a method
        | EAttribsMethod -- ^ attributes not allowed for method
        | EAttribsLocalFunction -- ^ attributes not allowed for local function
        | EAttribsImport -- ^ attributes not allowed for import
        | EAttribsExport -- ^ attributes not allowed for export
        | EAttribsForeignModule -- ^ attributes not allowed for foreign modules
        | EAttribsForeignFunction -- ^ attributes not allowed for foreign funcs
        | EAttribsTaskCall -- ^ attributes not allowed for task calls
        | EAttribsSeq -- ^ attributes not allowed for sequence
        | EAttribsThisDecl -- ^ attributes not allowed for this kind of declaration
        | EAttribsBVI -- ^ attributes not allowed for BVI statements
        | EAttribsCase -- ^ attributes not allowed for case statements
        | EAttribsSequence -- ^ attributes not allowed for sequence block
        | EAttribsProperty -- ^ attributes not allowed for sequence block
        | EAttribsAssert -- ^ attributes not allowed for assert statement
        | EAttribsExpect -- ^ attributes not allowed for expect statement
        | EAttribsAssume -- ^ attributes not allowed for assume statement
        | EAttribsCover -- ^ attributes not allowed for cover statement

        -- | "Attr <s1> is not supported for <s2>. Allowable one are: <ss>"
        | EBadAttributeName !String !String ![String]
        -- | "For attr <s1>, the arg is invalid; expected <s2>"
        | EBadAttributeValue !String !String
        | EMultipleAttribute !String -- ^ "Multiple <s> attributre are not support here"
        | EMultipleAssertionLabels

        -- XXX Is this not a form of EBadAttributeValue ?
        | EBadPortRenameAttributeString !String !String -- ^ "invalid string for attribute"
        -- XXX How is this different from EMultipleAttribute?
        | EDuplicatePortRenameAttribute !String !String -- ^ "duplicate attr S1 found in method S2"
        -- This is about port-renaming attributes not taking an argument
        -- XXX This is bogus!  There *is* an arg; it's boolean.
        | EAttributeArgNotAllowed !String
        | EEmptyPrefixNoPortName String
        | WPerhapsBadMethodName String
        | EConflictingGateAttr String
        | WUnusedPrefix String String  -- ^ kind of prefix and prefix string
        | WGateAllClocksIgnored
        | EAttributeOnWrongArgType String String String -- ^ attr, arg and reason
        | EAttributeNoSuchArg String String  -- ^ attr, bogus arg name
        | EPortsSameName [(String,Position,String)] -- ^ port name, position, arg
        | EPortKeywordClash String      -- ^ port name
        | EPortNotValidIdent String     -- ^ port name

        | EClockedByBadName String [String] -- ^ bad name, available names
        | EResetByBadName String [String] -- ^ bad name, available names

        -- | method s1 generates port s3 conflicting with method s2 at pos
        | EPortNamesClashFromMethod !String !String !String !Position
        | EPortKeywordClashFromMethod String String
        | EPortNotValidIdentFromMethod String String

        | EPortNamesClashArgAndIfc String String String Position

        | EExternalVarAssign !String -- ^ assignment to external var ... forbidden
        | ENonTerminalFunctionAssign !String !(Maybe String) -- ^ assignment to function ... must be last statement in block; perhaps you forgot ...?
        | ENonTerminalReturn !(Maybe String)  -- ^ return must be at end of block; perhaps you forgot ...?
        | ENonTerminalRules !(Maybe String)   -- ^ rules be at end of block; perhaps you forgot ...?
        | ENonTerminalMethodsOrSubinterfaces !(Maybe String) -- ^ methods must be at end of block; perhaps you forgot ...?
        | ENonTerminalNakedExpr !(Maybe String) -- ^ unassigned expression must be at end of block; perhaps you forgot ...?
        | ENonTerminalAction !(Maybe String) -- ^ unassigned action must be at end of block; perhaps you forgot ...?
        | ENonTerminalActionValue !(Maybe String) -- ^ unassigned actionvalue must be at end of block; perhaps you forgot ...?
        | EForbiddenFunctionAssign !String !String -- ^ function assign forbidden in this context
        | EBadStructUpdate !String -- ^ bad structure update -- XXX what does that mean???
        | EDuplicateDecl !String -- ^ duplicate declaration of ...
        | EDuplicateFunctionArg !String {- fct -} !String {- arg -} Position {- previous decl -} -- function ___ has duplicate argument ___ (previously used at ___)
        | EDuplicateMethodArg !String {- meth -} !String {- arg -} Position {- previous decl -} -- method ___ has duplicate argument ___ (previously used at ___)
        | EAssignBeforeDecl !String -- assign of ... before declaration
        | EUseBeforeAssign !String -- use of ... before assignment
        | ERegAssignToUninitializedLocal !String -- assign with <= to uninitialized local
        | EPatVarAssign !String -- assign to pattern variable ...
        | EAssignNotInAllPaths !String -- var assign not in all code paths
        | EInstanceInterfaceNameConflict String
        | ESequenceRequired !String -- seq or par construct required here
        | EForbiddenSequence !String -- seq or par construct forbidden here
        | EForbiddenRepeat !String -- repeat construct forbidden here
        | EForbiddenBreak !String -- break statement forbidden here
        | EForbiddenExpr !String !String
        | EForbiddenProvisos !String
        | EForbiddenMethod !String
        | EForbiddenReturn !String
        | EForbiddenLet !String
        | EForbiddenRule !String
        | EForbiddenRuleInAction
        | EForbiddenFunction !String
        | EForbiddenInstantiation !String
        | EForbiddenIf !String
        | EForbiddenFor !String
        | EForbiddenWhile !String
        | EForbiddenCase !String
        | EForbiddenNakedExpr !String
        | EForbiddenNakedExprInExprBlock
        | EForbiddenAction !String
        | EForbiddenActionValue !String
        | EForbiddenTypedef !String
        | EForbiddenTypeclass !String
        | EForbiddenInstanceDecl !String
        | EForbiddenInterface !String
        | EForbiddenModule !String
        | EForbiddenForeignModule !String
        | EForbiddenForeignFunction !String
        | EForbiddenExport !String
        | EForbiddenImport !String
        | EForbiddenTuple
        | EForbiddenDeriving
        | EForbiddenDeclaration !String
        | EForbiddenStatement
        | EEmptyRulePredicate !String -- ^ rule _ has () predicate; skip ()
        | EBadAssignEq !String
        | EBadAssignBind !String
        | EBadAssignRegWrite !String !(Maybe String) -- ^ <= bad in this context, perhaps you forgot ...
        | EBadAssignSubscript !String
        | EBadAssignField !String
        | EBadLValue
        | EBadPortProperty String String [String]
        | EBadFinalArg !String
        | EBadInterface
        | EBadSpecialArgs
        | EBadMethodConflictOp
        | EBadMethodConflictOpList
        | WNoSchedulingAnnotation [String] String [String]
        | ENestedModulePragma -- ^ pragmas not allowed in nested modules
        | ETerminalAction -- ^ action ends a block that requires a return value
        | EExprBlockWithoutValue -- ^ expression block missing return value
        | EActionValueWithoutValue -- ^ action value block without body
        | ESequenceIfPattern -- ^ pattern in if-condition in a sequence
        | ESequenceBind
        | WShadowDecl String Position -- ^ var name, previous declaration pos
        | WNeverAssigned String -- ^ variable was declared but not assigned
        | WDeprecated String String String -- ^ what, it's name, optional text
        | EObsolete String String String -- ^ what, it's name, optional text
        | MRestrictions String String  -- ^ please refer to the section on ____ in the Bluespec User Guide for restrictions on using ___
        | WExperimental String  -- ^ support for ___ is experimental
        | EDupMem -- ^ duplicate member in (struct, interface, union or typeclass)
            String -- ^ duplicate name
            String -- ^ kind of thing it is field, method, ...
            String -- ^ what it is in - struct, interface, ...
            String -- ^ name of the container (i.e. structure name, interface name, etc.)
        | EOverlappingTagEncoding
            String -- ^ type
            Integer -- ^ value being encoded to
            [(Position, String)] -- ^ names of conflicting tags
        | EAmbOper String String
        | EEmptyCase
        | ECaseNoMatch
        | EIfNoMatch
        | ETypesRequired !String
        | WTypesIgnored String
        | EForbiddenLetFn
        | EMultipleSpecialArgs
        | EInvalidNoOfClocks
        | EInvalidNoOfResetPorts
        | EUndeclaredClock String
        | EUndeclaredReset String
        | EDuplicateClocks String
        | EDuplicateResets String
        | EDuplicateIfcField String
        | EScheduleUnrelatedClocks
        | EScheduleNoClock
        -- see also EModuleUndet
        | EUndeterminedClock
        | EUseMissingDefaultClock
        | EUndeterminedReset
        | EUseMissingDefaultReset
        | EUndeterminedInout
        | EUndeterminedRules
        | EReservedClock String
        | EReservedReset String
        | EBVIDuplicateSchedule Position String [String] [String]
        | EBVISeparated
        | EBVIInvalidResets
        | EBVIMultipleOpts String
        | WBVIActionMethodNoClock [(String,Position)]
        | ETooManyDefaultClocks
        | ETooManyDefaultResets
        | EBVIInputOverlap String
        | EBVIInputOutputOverlap String
        | ESemiBeforeProvisos
        | ENoProvidedInterface
        | EEmptyEnum
        | EUniqueInst
        | ESplitAttributeHasANumberThatIsNotUnity !String !Integer
        | EConflictingSplitAttributes
        | EExpressionStatementContext
        | ESplitAttrUpd Bool [String]
        | ESplitAttrBinding Bool
        | ESplitAttrReturn Bool
        | ESplitAttrNonActionCtx Bool
        | EMissingFunctionBody

        -- Stmt Context
        | EUnsupportedCaseStmt !String

        -- SystemVerilog preprocessor errors
        | ESVPInvalidDefId String
        | ESVPInvalidDefIdKeyword String
        | ESVPRepeatedParamLabel String
        | ESVPUndefinedId String
        | ESVPWrongNumParams
            String -- ^ name
            Int -- ^ expected
            Int -- ^ found
        | ESVPUnmatchedEndIf
        | ESVPNoImportDelimiter
        | ESVPNoClosingParen String
        | ESVPNoId String
        | ENotUTF8

        -- Type checker and static elaboration errors

        | ECannotDerive String
        | EDeriveCtx String
        | ETypeSynRecursive [String]
        | EDuplicateInstance String Position
        | EBadInstanceOverlap String String Position

        | EUndefinedTask String
        | EUnboundCon String (Maybe String)
        | EUnboundVar String
        | EUnboundField String
        | EUnboundClCon String
        | EUnboundTyCon String
        | EUnboundTyVar String
        | EUnboundPackage String

        | EUnboundExport String Bool
        | EDuplicateExport String Bool
        | EDuplicateDefInPackageExport String String
        | ETypeNotExported
            String -- ^ missing export
            [(String, Position)] -- ^ id defined at pos uses type
        | EMultipleDecl
            String -- ^ var name
            Position -- ^ previous decl position

        | EForeignNotBit String
        | EPartialTypeApp String
        | ENotStructId String
        | ENotStructUpd String
        | ENotStruct String String
        | ENotField String String
        | EFieldsNotVis String
        | EFieldsNotImp String String
        | EDupField String
        | EFieldAmb [String] String
        | EConstrAmb String String
        | EConstrFieldsNotNamed String String -- ^ constructor, type

        | EUnify String String String
        | EUnifyKind String String String

        | EFuncMismatchResult  String String String  String String
        | EFuncMismatchNumArgs String String String  Integer Integer (Maybe Integer)
        | EFuncMismatchArgN    String String String  Integer String String
        | EFuncMismatchNoArgsExpected String String String
        | EFuncMismatchArgsExpected   String String String  Integer

        | EValueOf String
        | EStringOf String

        | ENumKindArg
        | EStrKindArg
        | ETypeNoArg String
        | ETypeTooManyArgs String
        | ETypeTooFewArgs String
        -- XXX we have O(n^2) of these for n kinds, this will get unmanagable if we add more kinds.
        -- Perhaps merge them into a single constructor parameterized by the names of the kinds?
        | EKindStarForNum String
        | EKindNumForStar String
        | EKindStrForNum String
        | EKindStrForStar String
        | EKindStarForStr String
        | EKindNumForStr String

        | EBoundTyVarKindMismatch String String Position String Position

        | EKindArg String
        | ETooGeneral String String
        | EWeakContext String [String] [(String, [Position], [String])] [(String, Position)]
        | EWeakCtxBitExtendNeedsAddCtx String [String] String [String] [Position]
        | EContextReduction String [Position] [(String, Position)]
        | EContextReductionReduces String [String] [Position] [(String, Position)]
        | ECtxRedWrongBitSize String Integer Integer [Position]
        | ECtxRedBitwiseBool [Position]
        | ECtxRedBitwise String [Position]
        | ECtxRedBitReduce String [Position]
        | ECtxRedBitExtendBadSizes Integer Integer [Position]
        | ECtxRedBitExtendBadType String [Position]
        | ECtxRedNotSelectable String [Position]
        | ECtxRedWrongSelectionResult String String String [Position]
        | ECtxRedNotUpdateable String [Position]
        | ECtxRedWrongUpdateArg String String String [Position]
        | ECtxRedNotWriteable String [Position]
        | ECtxRedWrongWriteArg String String String [Position]
        | ECtxRedBadSelectionIndex String [Position]
        | ECtxRedIsModule String [Position]
        | ECtxRedIsModuleActionValue [Position]
        | ENotNumEq String String [Position]
        | ECtxErrPrimParam String [Position] (Maybe [String])
        | ECtxErrPrimPort String [Position] (Maybe [String])
        | EClassFundepsNotFull String [String] [([String], [String])]
        | EClassFundepsOverlap String
        | EClassFundepsExtra String [String]
        | EClassFundepsEmpty String
        | WIncoherentMatch String String
        | WOrphanInst String
        | EModInstWrongArgs [Position]
        | EAmbiguous [(String, Position, [Doc])]
        | EAmbiguousExplCtx [Doc] [Doc] Doc
        | EWrongArity
        | EUnknownSize
        | EBadExtractSize Integer
        | EBadExtractIndex Integer
        | ENotExpr
        | ELocalRec [String]
        | ENotAnInterface
        | ENotModule String
        | EPolyField
        | ENotKNum String
        | EBadGenArg String
        | EBadIfcType String String
        | EBadForeignIfcType String
        | ENoTypeSign String
        | EStmtContext String
        | EBadMatch String
        | EBitSel String String String String
        | EMultipleInterfaces
        | EMissingFileArgument String String String
        | EBadVeriType String

        | EInvalidLiteral String Integer String
        | EInvalidSizedLiteral String Integer

        | ETooManySteps String String
        | WTooManySteps String Integer Integer Integer
        | EStepsIntervalError String Integer Integer

        | WMissingField String

        | EForeignModBadArgType
            String -- ^ type
            String -- ^ mod
            String -- ^ mod_position
        | EForeignModBadResType
            String -- ^ type
            String -- ^ mod
            String -- ^ mod_position
        | EForeignModTooManyPorts
            String -- ^ method_name
        | EForeignModTooFewPorts
            String -- ^ method_name
        | EForeignModEmptyBody
        | EForeignModOutputOrEnable
            String -- ^ method_name
        | EForeignModMissingValuePort String String String
        | EForeignModMissingEnablePort String String String
        | EForeignModUnexpectedValuePort String String String
        | EForeignModUnexpectedEnablePort String String String
        | EForeignModNotClockType String String String String
        | EForeignModNotResetType String String String String
        | EForeignModNotInoutType String String String String
        | EForeignModClockHasArgs String String String
        | EForeignModResetHasArgs String String String
        | EForeignModInoutHasArgs String String String
        | EForeignModNotField String String
        | EForeignModMissingField String String String
        | EForeignModSynth String

        | EForeignFuncStringRes
        | EForeignFuncBadArgType
            [(String,Bool)] -- ^ types and which are poly
        | EForeignFuncBadResType
            String -- ^ type
            Bool   -- ^ is type poly
        | EForeignFuncDuplicates String [(String,Position)]

        | ENoInlineAction String
        | ENoInlineContext String
        | ENoInlinePolymorphic String

        | ETypeStackOverflow
        | ETypeSuperStackOverflow
        | ERecursiveBits String String

        -- Type mismatch with assignment operator
        | EAssignNotReg String

        | EMethodArgNameMismatch String [(String,String)]

        | EActionSelfSB [String]
        | ETaskMismatchNumArgs String String Integer

        -- Generation errors (including scheduling)

        | EHasWhen String

        | EFewPorts String String Integer Integer
        -- EResources (method id) (max ports) calls@[(expr,position)]
        | EResources String Integer [(String,String)]
        | EArbitrate String [String] -- module id, rule ids
        -- ECrossDomainMethodUse (method id) calls@[(expr,position)]
        | ECrossDomainMethodUse String [(String,String)]

        | EParActionRangeConflict String
              (String, Maybe Doc, Doc, Bool)
              (String, Maybe Doc, Doc, Bool)

        | EDynamicExecOrderOneRule String [(String, String, [String])]
        | EDynamicExecOrderTwoRules String String
              [(String, String, [String])]
              [String] [Doc]
        | EDynamicExecOrderTwoRulesBothDir String String
              [(String, String, [String])]
              [(String, String, [String])]
        | EDynamicExecOrderTwoRulesLoop [String] [Doc]

        | ERuleAssertion
            String -- ^ rule id
            String -- ^ assertion
            (Maybe Doc) -- ^ reason
        | ENotAlwaysReady String

        | EClockDomain String String [[(String, [(String, Position)])]]
        | EClockArgSiblings String String [(String, String)]
        | EClockArgAncestors String String [(String, String)]
        | WClockOfClocks [[(String, [(String, Position)])]]

        | EResetClocks String String [(String, String)]
        | WMultipleResets String String [(String, [(String, Position)])]
        | WResetOfResets [(String, [(String, Position)])]
        | EInResetToMultipleDomainArgs String String String [(String, String)]

        | EPortExprClockDomain String (Maybe ([String], [String])) [String]
        | WPortExprReset String String [(String, Position)]

        | EInoutExprClockDomain String (Maybe ([String], [String]))
                                       (Maybe [String])
        | WInoutExprReset String String

        -- for methods whose clock/reset is not on the boundary
        | EMethodNoBoundaryClock String
        | WMethodNoBoundaryReset String
        -- for in/out resets whose associated domain is not on the boundary
        | WOutputResetNoBoundaryClock String
        | WInputResetNoBoundaryClock String
        -- for inout interface
        | WIfcInoutNoBoundaryClock String
        | WIfcInoutNoBoundaryReset String
        -- cannot express multiple resets on a boundary (method, chosen reset)
        | WMethodMultipleBoundaryReset String (Maybe String)

        | EClkGateNotInhigh String String String
        | EClkGateNotUnused String

        | EAttributeIdNotAMethod String
        | EAttributeIdNotAnInputClock String

        | EModParameterDynamic String String
        | EParamOnlyType String String
        | EDynamicInputClock String String
        | EDynamicInputReset String String
        | EDynamicArgInout String String

        | EDynamicClock
        | EDynamicReset
        | EDynamicInout
        | EDynamicRules
        | EDynamicModule

        | EBSimMCDUnsupported String
        | EBSimDynamicArg String [String]
        | EBSimTopLevelArgOrParam Bool [String]
        | EBSimEnablePragma
        | EBSimForeignImport String String String
        | EBSimInoutIfc [String]
        | EBSimInoutArg (Maybe String) [String]
        | EBSimSplitMethods [String]

        | EDivideByZero
        | EIntegerNegativeExponent
        | EInvalidLog
        | EInvalidLogBase
        | EInvalidLogOneOne
        | ENegativeSqrt
        | EAddPosAndNegInfinity
        | EMultiplyZeroAndInfinity
        | EFloatNaN

        | EStringToChar String
        | EIntegerToChar Integer

        | EUnexpectedOutputClkGate String

        | EInterfaceArg String

        | ECrossDomainPragma [String]

        | WCycleDrop String String [String]
        | WUrgencyChoice { em_more_urgent :: Doc,
                           em_less_urgent :: Doc,
                           em_conflicts :: Doc }
        | WEarlinessChoice { em_more_early :: Doc,
                             em_less_early :: Doc,
                             em_conflicts :: Doc }
        | WActionShadowing String String [String]
        | EMERulesIdentical String String
        | WRuleNeverFires String Bool
        | WRuleAlwaysFalse String Bool
        | WRuleNoActions String Bool
        | WRuleUndetPred Bool String [Position]
        | WMethodNeverReady String
        | WNoScheduleDump String [String]

        | WMethodAnnotChange String String [String]
        | WSATNotAvailable String String (Maybe String)

        | EModuleUndet
        | EModuleUndetNoMatch
        | EStringNF String
        | EStringListNF String
        | ENoNF String String
        | EHasImplicit String
        | EModPortHasImplicit String String
        | EModuleLoop String

        | EEnableNotHigh String [String]
        | EEnableAlwaysLow String [String]

        | ESplitInsideNoSplit String

        | WMissingRule String

        | WFCall [(String, Position, [Position])]

        | ECombCycle [String]

        | ENetInstConflict String

        | EUninitialized String -- ^ declared but not initialized (BSV only)

        | EUnknownRuleId String
        | EUnknownRuleIdAttribute String
        | WInlinedMethodIdAttribute String

        | EUrgencyCycle
            [String] -- ^ cycle
            [Doc]    -- ^ explanation of edges
            [String] -- ^ other rules in the SCC
        | EPreSchedCycle
            Doc -- ^ description of the cycle
        | ESelfUrgency
            String -- ^ ruleId
            Doc --  ^ description of the path
        | EPathMethodArgToRdy
            String -- ^ method
            String -- ^ arg
            Doc -- ^ descr of path
        | EPathMethodEnToRdy
            String -- ^ method
            Doc -- ^ description of path

        | EReflexiveUserUrgency
            String -- ^ id
            Position -- ^ pos1
            Position --  ^ pos2

        | ECombinedSchedCycle
            [String] -- ^ cycle
            [Doc] -- ^ explanation of edges
            [String] -- ^ other rules in the SCC
        | EMethodSchedToExec
            String -- ^ method
            [String] -- ^ cycle
            [Doc] -- ^ explanation of edges

        | EInvalidWhen

        -- System errors (including flags and file handling)

        | EFileReadFailure String String  -- filename, error description
        | EFileWriteFailure String String  -- filename, error description
        | EFileRemoveFailure String String -- filename, error description
        | EFileCopyFailure String String String -- src, dst, error description
        | EDirCreateFailure String String  -- dirname, error description
        | EFileHandleFailure String -- error description

        | WFileExistsButUnreadable String String -- filename, error description
        | WMultipleFilesInPath String [String]

        | EMissingPackage String
        | WFilePackageNameMismatch String String
        -- Use EFileReadFailure instead of this:
        -- EFailOpenSrcFile String String  -- filename, error description
        -- The arguments are the missing filename and the package it is for
        | EMissingBinFile String String
        | EMissingIfcFile String String
        | EMissingIncludeFile String
        | EBinFileVerMismatch String
        | EBinFileSignatureMismatch String String
        | EBinFileSignatureMismatch2 String String String
        | EBinFilePkgNameMismatch String String String -- file, expected, found
        | ENoEntryPoint
        | ECircularImports [String]
        | ECircularImportsViaBinFile String String

        | EUnknownFlag String
        | EDupKillFlag String String
        | ENotToggleFlag String
        | ENoArgFlag String
        | EOneArgFlag String
        | ETwoArgFlag String
        | EIntegerArgFlag String
        | EPositiveIntegerArgFlag String
        | EFloatArgFlag String
        | EMsgListArgFlag String String
        | EBadArgFlag String String [String]
        | EExactlyOneArgRequired String [String]
        | WDeprecatedFlag String String
        | WDuplicatePathDirs String String Bool [String]
        | WOpenPathDirFailure String String String -- flag, dir, msg
        | EOpenOutputDirFailure String String String -- flag, dir, msg

        | ENoBackendCodeGen [String]
        | ENoBackendLinking
        | ETooManyBackends
        | EDollarNoVerilog
        | EDollarLink
        | EWrongBackend String String
        | ENoOptUndetNoXZ String

        | ELinkFilesWithSrc String [String]
        | EVerilogFilesWithSimBackend [String]
        | EVPIFilesWithNoABin [String]
        | EGenNamesForLinking [String]
        | EEntryForCodeGen String

        | EUnknownSrcExt String
        | ENoSrcExt String
        | EMixedSrcFiles
        | EFlagAfterSrc String
        | ENotVerSrcFile String
        | ENotCSrcFile String
        | EMultipleSrcFiles
        | EMissingUserFile String [String]
        | EUnrecognizedCmdLineText String
        | EUnknownVerilogSim String [String] Bool
        | EMissingVPIWrapperFile String Bool

        -- ABin (.ba) file issues
        | WExtraABinFiles [String]
        | EMissingABinModFile String (Maybe String)
        | EMissingABinForeignFuncFile String String
        | EMultipleABinFilesForName String [String]
        | EABinFileBackendMismatch String String String
        | EWrongABinTypeExpectedModule String (Maybe String)
        | EWrongABinTypeExpectedForeignFunc String String
        | EABinNameMismatch String String String
        | EABinModSchedErr String (Maybe String)
        | ECircularABin String [(String, String)]

        -- Bluesim-specific errors/warnings
        | EBluesimNoXZ String

        -- Errors/warnings from the SystemC wrapper generator
        | ESystemCWrapperComboPaths String
        | ESystemCWrapperInvalidMethods [String]
        | ESystemCWrapperRuleBeforeMethod [(Doc,Doc)]

        -- ASSERTIONS
        | EForbiddenSequenceDecl !String !String
        | EForbiddenPropertyDecl !String !String
        | EForbiddenAssert !String
        | EForbiddenAssume !String
        | EForbiddenCover !String
        | EForbiddenExpect !String
        | EWrongParamNumber Int Int
        | EIllegalAssertExpr !String !String
        | EIllegalAssertStmt !String
        | EIllegalAssertDelayRange !String !String
        | EUnsupportedSequence  --These will be removed once supported
        | EUnsupportedProperty
        | EUnsupportedAssertion
        | EUnsupportedMutualRecursion [String]
        | EMutualRecursionComplicatedClause String
        | EIllegalRepetition !String

        -- System assumptions
        | EFloatingPointNotIEEE
        | EFloatingPointRadixNotTwo
        | EFloatingPointPrecisionNot53
        | EDoubleNot64Bit

        -- Runtime errors (mainly to share printing infrastructure)
        | EMutuallyExclusiveRulesFire String String
        | EConflictFreeRulesFail (String, String) String (String, String)

        | EVerilogFilterError String String Int
        -- This should be obsoleted
        | EGeneric String -- ^ make your own error message
        -- | Tagged "generate" error
        | EGenerate Integer String
        -- | use of a definition that didn't compile
        | EPoisonedDef !Doc
        -- | a .bo file contains a poison-pill
        | WPoisonedDefFile String
        -- | warnings were suppressed
        | WSuppressedWarnings Integer
        -- | request to demote an error could not be obeyed
        | WNonDemotableErrors [String]

        | EPortNameErrorOnImport String String
        | ENoTopTypeSign String
        | WUnusedDef String
        | EConPatArgs String (Maybe String) Int Int

        -- XXX these should contain the type of the constructor
        | EConMismatchNumArgs  String{-String-}      Integer Integer
        | EPartialConMismatchNumArgs  String String{-String-}Integer Integer Integer
        deriving (Eq,Show)

instance PPrint ErrMsg where
    pPrint _ _ e = text (show e)

-- | Errors are in one of five categories:
data ErrMsgTag =
    -- | Parse errors (literally, the first pass of compilation,
    --   so in BSV some type checking will be encorporated here)
      Parse    Integer
    -- | Errors in the type checking and static elaboration
    | Type     Integer
    -- | File handling problems, flags errors, other system errors
    | System   Integer
    -- | Errors in the back-end (including scheduling)
    | Generate Integer
    -- | Errors detected during simulation (runtime)
    | Runtime  Integer
    deriving (Eq, Show)

errMsgTagWidth :: Integer
errMsgTagWidth = 4

prErrMsgTag :: ErrMsgTag -> String
prErrMsgTag (Parse    i) = ('P' : integerFormat errMsgTagWidth 10 i)
prErrMsgTag (Type     i) = ('T' : integerFormat errMsgTagWidth 10 i)
prErrMsgTag (System   i) = ('S' : integerFormat errMsgTagWidth 10 i)
prErrMsgTag (Generate i) = ('G' : integerFormat errMsgTagWidth 10 i)
prErrMsgTag (Runtime  i) = ('R' : integerFormat errMsgTagWidth 10 i)

getErrMsgTag :: ErrMsg -> String
getErrMsgTag m = prErrMsgTag $ fst3 (getErrorText m)

showEMsgList :: String -> MsgContext -> [EMsg] -> String
showEMsgList ekind ctx ms = pretty 78 78 (prEMsgList ekind ctx ms)

showErrorList :: [EMsg] -> String
showErrorList   = showEMsgList serror emptyContext

showWarningList :: [EMsg] -> String
showWarningList = showEMsgList swarning emptyContext

showMessageList :: [EMsg] -> String
showMessageList = showEMsgList smessage emptyContext

showErrorListWithContext :: MsgContext -> [EMsg] -> String
showErrorListWithContext   = showEMsgList serror

showWarningListWithContext :: MsgContext -> [EMsg] -> String
showWarningListWithContext = showEMsgList swarning

-- note that this sorts the messages by position
prEMsgList :: String -> MsgContext -> [EMsg] -> Doc
prEMsgList ekind ctx ms = vcat (map (prEMsg ekind ctx) (sortBy cmpEMsg ms))
  where cmpEMsg (pos1, _) (pos2, _) = compare pos1 pos2

prEMsg :: String -> MsgContext -> EMsg -> Doc
prEMsg ekind@(l:ls) ctx (p,m) =
    let
        (tag, _ {-short_text-}, long_text) = getErrorText m
        cap_ekind = (toUpper l:ls)
        errtag = char '(' <> text (prErrMsgTag tag) <> char ')'
    in
        -- Currently, we do not print the short description
        (text cap_ekind <> char ':' <+>
         text (prPosition p) <> char ':' <+> errtag) $$
        nest 2 long_text $$
        nest 2 ctx
prEMsg "" _ _ = internalError "Error.prEMsg \"\" _"


--
-- Do not call this outside of Error.hs!
--
-- This function returns a tag, a short message, and a long message.
--
getErrorText :: ErrMsg -> (ErrMsgTag, Doc, Doc)

-- Parse errors

getErrorText EBadCharLit =
    (Parse 0, empty, s2par "Bad Char literal")
getErrorText EBadStringLit =
    (Parse 1, empty, s2par "Bad String literal")
getErrorText (EBadLexChar c) =
    (Parse 2, empty, s2par ("Bad character in input: " ++ show c))
getErrorText (EUntermComm p) =
    (Parse 3, empty, s2par ("Unterminated block comment, started at " ++ prPosition p))
getErrorText EMissingNL =
    (Parse 4, empty, s2par "Missing newline after -- comment")
getErrorText (ESyntax s []) =
    (Parse 5, empty, s2par ("Unexpected " ++ s))
getErrorText (ESyntax s ss) =
    (Parse 5, empty, s2par ("Unexpected " ++ s ++ "; expected " ++ unwordsOr ss))
--getErrorText (ESyntaxUnknown) =
--    (Parse 6, empty, s2par "unknown parse error (BSC BUG)")

getErrorText (EUnsupportedBitVector) =
    (Parse 7, empty, s2par "Only [N:0] bit vectors supported")
getErrorText (EUnsupportedImport pkg var) =
    (Parse 8, empty, fsep ([text "Importing", text (ishow (pkg ++ "::" ++ var))] ++
                           s2docs "not supported; use" ++ [text (ishow (pkg ++ "::*"))]))
getErrorText (EMissingProvisoArgs tclass) =
    (Parse 9, empty, s2par ("Missing proviso arguments for typeclass " ++ ishow tclass))
getErrorText (EAttribsTypedef) =
    (Parse 10, empty, s2par "Attributes not allowed for typedef")
getErrorText (EAttribsTypeclass) =
    (Parse 11, empty, s2par "Attributes not allowed for typeclass")
getErrorText (EAttribsInstance) =
    (Parse 12, empty, s2par "Attributes not allowed for instance")
getErrorText (EAttribsVarDef) =
    (Parse 13, empty, s2par "Attributes not allowed for variable definition")
getErrorText (EAttribsIfcDecl) =
    (Parse 14, empty, s2par "Attributes not allowed for interface declaration")
getErrorText (EAttribsBeginEnd) =
    (Parse 15, empty, s2par "Attributes not allowed for begin ... end block")
getErrorText (EAttribsAction) =
    (Parse 16, empty, s2par "Attributes not allowed for action block")
getErrorText (EAttribsActionValue) =
    (Parse 17, empty, s2par "Attributes not allowed for actionvalue block")
getErrorText (EAttribsReturn) =
    (Parse 18, empty, s2par "Attributes not allowed for \"return\"")
getErrorText (EAttribsIf) =
    (Parse 19, empty, s2par "Attributes not allowed for if-statement")
getErrorText (EAttribsFor) =
    (Parse 20, empty, s2par "Attributes not allowed for for-statement")
getErrorText (EAttribsWhile) =
    (Parse 21, empty, s2par "Attributes not allowed for while-statement")
getErrorText (EAttribsMethod) =
    (Parse 22, empty, s2par "Attributes not allowed for method")
getErrorText (EAttribsLocalFunction) =
    (Parse 23, empty, s2par "Attributes not allowed for non-top-level function")
getErrorText (EAttribsImport) =
    (Parse 24, empty, s2par "Attributes not allowed for import statement")
getErrorText (EAttribsTaskCall) =
    (Parse 25, empty, s2par "Attributes not allowed for task calls")
getErrorText (EAttribsSeq) =
    (Parse 26, empty, s2par "Attributes not allowed for sequences")
getErrorText (EAttribsThisDecl) =
    (Parse 27, empty, s2par "Attributes not allowed for this kind of declaration")
getErrorText (EExternalVarAssign var) =
    (Parse 28, empty, s2par ("Assignment to external variable " ++ ishow var ++ " forbidden"))
getErrorText (ENonTerminalFunctionAssign func maybeMissing) =
    (Parse 29, empty, s2par ("Assignment to function " ++ ishow func ++ " must be at end of block"))
getErrorText (ENonTerminalReturn maybeMissing) =
    (Parse 30, empty, s2par (quote "return" ++ " must be at end of block" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (ENonTerminalRules maybeMissing) =
    (Parse 31, empty, s2par ("Rules must be at end of block" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (ENonTerminalMethodsOrSubinterfaces maybeMissing) =
    (Parse 32, empty, s2par ("Methods and subinterfaces must be at end of block" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (ENonTerminalNakedExpr maybeMissing) =
    (Parse 33, empty, s2par ("Unassigned expressions must be at end of block" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (ENonTerminalAction maybeMissing) =
    (Parse 34, empty, s2par ("Unassigned action must be at end of block" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (ENonTerminalActionValue maybeMissing) =
    (Parse 35, empty, s2par ("Unassigned actionvalue must be at end of block" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (EForbiddenFunctionAssign func context) =
    (Parse 36, empty, s2par ("Assignment to function " ++ ishow func ++ " forbidden in " ++ context ++ " context"))
getErrorText (EBadStructUpdate struct) =
    (Parse 37, empty, s2par ("Bad update of struct " ++ ishow struct))
getErrorText (EDuplicateDecl var) =
    (Parse 38, empty, s2par ("Duplicate declaration of " ++ ishow var))
getErrorText (EAssignBeforeDecl var) =
    (Parse 39, empty,
      s2par ("Assignment of " ++ ishow var ++ " without declaration, " ++
             "or non-local assignment in possibly wrong context " ++
             "(e.g. declared at evaluation time, maybe updated at runtime, " ++
             "perhaps you meant \"<=\" instead, etc.)"))
getErrorText (EUseBeforeAssign var) =
    (Parse 40, empty, s2par ("Use of " ++ ishow var ++ " without assignment"))
getErrorText (EPatVarAssign var) =
    (Parse 41, empty, s2par ("Assignment to pattern variable " ++ ishow var))
getErrorText (EAssignNotInAllPaths var) =
    (Parse 42, empty, s2par ("Assignment to " ++ ishow var ++ " missing from some paths"))

getErrorText (EForbiddenMethod context) =
    (Parse 43, empty, s2par ("Methods forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenReturn context) =
    (Parse 44, empty, s2par (quote "return" ++ " forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenRule context) =
    (Parse 45, empty, s2par ("Rules forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenFunction context) =
    (Parse 46, empty, s2par ("Functions forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenInstantiation context) =
    (Parse 47, empty, s2par ("Instantiations forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenIf context) =
    (Parse 48, empty, s2par ("if-statements forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenFor context) =
    (Parse 49, empty, s2par ("for-statements forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenWhile context) =
    (Parse 50, empty, s2par ("while-statements forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenCase context) =
    (Parse 51, empty, s2par ("case-statements forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenNakedExpr context) =
    (Parse 52, empty, s2par ("Unassigned expressions forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenAction context) =
    (Parse 53, empty, s2par ("Actions forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenActionValue context) =
    (Parse 54, empty, s2par ("Action-values forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenTypedef context) =
    (Parse 55, empty, s2par ("Typedefs forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenTypeclass context) =
    (Parse 56, empty, s2par ("Type classes forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenInstanceDecl context) =
    (Parse 57, empty, s2par ("Instance declarations forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenInterface context) =
    (Parse 58, empty, s2par ("Interfaces forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenModule context) =
    (Parse 59, empty, s2par ("Modules forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenForeignModule context) =
    (Parse 60, empty, s2par ("Foreign modules forbidden in " ++ context ++ " context"))
-- Removed Parse 61 obsoleted by EBadAttributeName
getErrorText (EForbiddenStatement) =
    (Parse 62, empty, s2par ("Invalid statement in this context"))
getErrorText (EBadAttributeValue name expected) =
    (Parse 63, empty,
     s2par ("For attribute " ++ quote name ++
            ", the attribute value is invalid; expected " ++ expected ++ "."))
getErrorText (EBadAssignEq context) =
    (Parse 64, empty, s2par ("Assignment with " ++ quote "=" ++ " forbidden in " ++ context ++ " context"))
getErrorText (EBadAssignBind context) =
    (Parse 65, empty, s2par ("Assignment with " ++ quote "<-" ++ " forbidden in " ++ context ++ " context"))
getErrorText (EBadAssignRegWrite context maybeMissing) =
    (Parse 66, empty, s2par ("Assignment with " ++ quote "<=" ++ " forbidden in " ++ context ++ " context" ++ missingEndKeywordSuggestion maybeMissing))
getErrorText (EBadLValue) =
    (Parse 67, empty, s2par "Invalid left-hand-side of assignment")
getErrorText (EBadPortProperty loc prop allowed) =
    (Parse 68, empty,
     s2par ("The port property " ++ quote prop ++
            " is not allowed on " ++ loc ++ ". " ++
            "Allowable properties are:" ) <+>
     quoteStrList allowed <> text "."
     )
getErrorText (ETerminalAction) =
    (Parse 69, empty, s2par "Action terminates a block that requires a return value")
getErrorText (EExprBlockWithoutValue) =
    (Parse 70, empty, s2par "Expression block (starting around here) missing return value")
getErrorText (EActionValueWithoutValue) =
    (Parse 71, empty, s2par "actionvalue block missing return value")
getErrorText (WDeprecated i_type i msg) =
    (Parse 72, empty,
     s2par ("The " ++ i_type ++ " " ++ ishow i ++ " is deprecated.  " ++ msg))

getErrorText (EDupMem name element container_type container_name) =
    (Parse 73, empty, s2par $ "Duplicate definition of " ++ element ++ " " ++
                              ishow name ++ " in " ++ container_type ++ " " ++
                              ishow container_name)
getErrorText (EAmbOper op1 op2) =
    (Parse 74, empty, s2par $ "Ambiguous operator combination with "++op1++" and "++op2++".")
getErrorText EEmptyCase =
    (Parse 75, empty, s2par "Case statement with no clauses")
getErrorText (ECaseNoMatch) =
    (Parse 76, empty, s2par "No arms matched in case statement without a default arm")
getErrorText (EIfNoMatch) =
    (Parse 77, empty, s2par "Test failed in if statement without an else arm")
getErrorText (EForbiddenImport context) =
    (Parse 78, empty, s2par ("Imports forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenExport context) =
    (Parse 79, empty, s2par ("Exports forbidden in " ++ context ++ " context"))
getErrorText (EAttribsForeignModule) =
    (Parse 80, empty, s2par "Attributes not allowed for foreign modules")
getErrorText (EAttribsExport) =
    (Parse 81, empty, s2par "Attributes not allowed for exports")
getErrorText (ENestedModulePragma) =
    (Parse 82, empty, s2par "Attributes not allowed for non-toplevel modules")

getErrorText (ESequenceRequired context) =
    (Parse 83, empty, s2par ("seq, par or action construct required in " ++ context ++ " context, not begin/end"))
getErrorText (EForbiddenSequence context) =
    (Parse 84, empty, s2par ("seq and par constructs forbidden in " ++ context ++ " context"))
getErrorText (EDuplicateFunctionArg fct arg prevPos) =
    (Parse 85, empty, s2par ("Function " ++ ishow fct ++ " has duplicate argument " ++ ishow arg ++ " (previous declaration at " ++ prPosition prevPos ++ ")"))
getErrorText (EDuplicateMethodArg fct arg prevPos) =
    (Parse 86, empty, s2par ("Method " ++ ishow fct ++ " has duplicate argument " ++ ishow arg ++ " (previous declaration at " ++ prPosition prevPos ++ ")"))
getErrorText (EForbiddenProvisos context) =
    (Parse 87, empty, s2par ("Provisos forbidden in " ++ context ++ " context"))
getErrorText (ETypesRequired var) =
    (Parse 88, empty, s2par ("Explicit type required for " ++ ishow var))
getErrorText (EForbiddenLetFn) =
    (Parse 89, empty,
     s2par ("Functions with incomplete type forbidden at top level"))
getErrorText (EBadLineDirective) =
    (Parse 90, empty, s2par "Malformed `line directive")
getErrorText (EBadStringEscapeChar c) =
    (Parse 91, empty, s2par ("Bad string escape char: " ++ quote [c]))
getErrorText (EStringNewline) =
    (Parse 92, empty, s2par "Newline in string literal")
getErrorText (EStringEOF) =
    (Parse 93, empty, s2par "File ends inside string literal")
getErrorText (EBadSymbol op) =
    (Parse 94, empty, s2par ("Unknown symbol: " ++ quote op))
getErrorText (EForbiddenTuple) =
    (Parse 95, empty, s2par "Tuple not allowed here, or wrong length")
getErrorText (EUnsupportedNumReal num) =
    (Parse 96, empty, s2par ("Fractional numeric literals not supported: " ++ quote num))
getErrorText (EUnsupportedNumUndetermined num) =
    (Parse 97, empty, s2par ("Numeric literals with X or Z not supported: " ++ quote num))
getErrorText (EUnsupportedPatAll1 num) =
    (Parse 98, empty, s2par ("Undetermined number of 1 bits not supported in pattern: " ++ quote num))
getErrorText (ESequenceIfPattern) =
    (Parse 99, empty, s2par ("Conditions in a sequence if-statement may not be patterns"))
-- Removed Parse 100 obsoleted by EBadAttributeName
getErrorText (EInstanceInterfaceNameConflict name) =
    (Parse 101, empty,
     s2par ("Instance and interface names must differ for " ++ quote name))
getErrorText (WShadowDecl name prevPos) =
    (Parse 102, empty, s2par ("Declaration of " ++ quote name ++
                              " shadows previous declaration at " ++
                              prPosition prevPos))
getErrorText (WNeverAssigned var) =
    (Parse 103, empty, s2par (quote var ++ " declared but never assigned"))
getErrorText (ERegAssignToUninitializedLocal var) =
    (Parse 104, empty, s2par ("Register assignment to uninitialized local" ++
                              " variable " ++ quote var ++
                              "; perhaps you meant \"=\"?"))
getErrorText (EForbiddenRuleInAction) =
    (Parse 105, empty, s2par
     ("Rules forbidden in action context; perhaps an " ++ quote "endrule" ++
      " is missing from a previous rule?"))
getErrorText (EForbiddenNakedExprInExprBlock) =
    (Parse 106, empty, s2par ("Unassigned expressions forbidden in expression block; perhaps " ++ quote "return" ++ " is missing before the expression?"))
getErrorText (EBadFinalArg a) =
    (Parse 107, empty, s2par ("Final arg should be provided interface name, not " ++ quote a))
getErrorText (EMultipleSpecialArgs) =
    (Parse 108, empty, s2par ("Multiple clockedby, resetby or poweredby args"))
getErrorText (EForbiddenDeriving) =
    (Parse 109, empty,
     s2par ("Deriving typeclasses not permitted for nested structures"))
getErrorText (EBadInterface) =
    (Parse 110, empty,
      s2par ("This module must have an explicit interface type, or an explicit interface"))
getErrorText (EBadMethodConflictOp) =
    (Parse 111, empty,
      s2par ("Invalid scheduling operator"))
getErrorText (EInvalidNoOfClocks) =
    (Parse 112, empty,
      s2par ("Invalid number of clock wires (1 or 2 required)"))
-- ASSERTIONS
getErrorText (EForbiddenSequenceDecl context s) =
    (Parse 113, empty,
     s2par ("Sequence declarations are not permitted in " ++ context ++ " context: "
            ++ ishow s))
getErrorText (EForbiddenPropertyDecl context s) =
    (Parse 114, empty,
     s2par ("Property declarations are not permitted in " ++ context ++ " context: "
            ++ ishow s))
getErrorText (EForbiddenAssert context) =
    (Parse 115, empty,
     s2par ("Assertion statements are not permitted in " ++ context ++ " context"))
getErrorText (EForbiddenAssume context) =
    (Parse 116, empty,
     s2par ("Assume statements are not permitted in " ++ context ++ " context"))
getErrorText (EForbiddenCover context) =
    (Parse 117, empty,
     s2par ("Cover statements are not permitted in " ++ context ++ " context"))
getErrorText (EForbiddenExpect context) =
    (Parse 118, empty,
     s2par ("Expect statements are not permitted in " ++ context ++ " context"))
getErrorText (EUnsupportedSequence) =
    (Parse 119, empty,
     s2par ("Sequence declarations are not currently supported"))
getErrorText (EUnsupportedProperty) =
    (Parse 120, empty,
     s2par ("Property declarations are not currently supported"))
getErrorText (EUnsupportedAssertion) =
    (Parse 121, empty,
     s2par ("assert, assume, cover, and expect statements are not currently supported"))
getErrorText (EWrongParamNumber def given) =
    (Parse 122, empty,
     s2par ("Wrong number of parameters to sequence or property instance (Defined: " ++ (show def) ++  ", Given: " ++ (show given) ++ ")"))
getErrorText (EIllegalAssertExpr exp context) =
    (Parse 123, empty,
     s2par ("Illegal expression " ++ exp ++ " in " ++ context ++ " context"))
getErrorText (EIllegalAssertStmt context) =
    (Parse 124, empty,
     s2par ("Illegal statement in " ++ context ++ " context. Only assignments, system tasks, and value functions are allowed"))
getErrorText (EIllegalRepetition rep) =
    (Parse 125, empty,
     s2par (rep ++ " may only follow simple boolean expressions"))
-- Removed Parse 126 obsoleted by EBadAttributeName
getErrorText (EForbiddenLet context) =
    (Parse 127, empty, s2par (quote "let" ++ " forbidden in " ++ context ++ " context"))
getErrorText (EBadAssignSubscript context) =
    (Parse 128, empty, s2par ("Array element assignments forbidden in " ++ context ++ " context"))
getErrorText (EBadAssignField context) =
    (Parse 129, empty, s2par ("Struct/union field assignments forbidden in " ++ context ++ " context"))
getErrorText (EIllegalAssertDelayRange exp description) =
    (Parse 130, empty,
     s2par ("Illegal assertion delay range " ++ exp ++ ". " ++ description))
getErrorText (EBVISeparated) =
    (Parse 131, empty, s2par ("BVI statements must all be together at end of BVI block"))
getErrorText (EBVIInvalidResets) =
    (Parse 132, empty, s2par ("invalid reset specification in BVI block"))
-- Removed Parse 133 (EForbiddenDummyId) b/c "_" variable name is now valid BSV
getErrorText (EUndeclaredClock clk_name) =
    (Parse 134, empty, s2par ("undeclared clock " ++ quote clk_name))
getErrorText (EForeignModEmptyBody) =
    (Parse 135, empty, s2par ("foreign module definition has empty body"))
getErrorText (EEmptyRulePredicate rule_name) =
    (Parse 136, empty, s2par
     ("Empty () for rule condition forbidden: for true condition, " ++
     "remove () in rule \"" ++ rule_name ++ "\""))
getErrorText (EUndeclaredReset rst_name) =
    (Parse 137, empty, s2par ("undeclared reset " ++ quote rst_name))
getErrorText (EInvalidNoOfResetPorts) =
    (Parse 138, empty,
      s2par ("More than one reset wire specified"))
getErrorText (ETooManyDefaultClocks) =
    (Parse 139, empty,
      s2par ("More than one default clock specified"))
getErrorText (ETooManyDefaultResets) =
    (Parse 140, empty,
      s2par ("More than one default reset specified, or no_reset also specified"))
getErrorText (ESemiBeforeProvisos) =
    (Parse 141, empty,
      s2par ("Provisos following (probably superfluous) semicolon"))
getErrorText (ESVPInvalidDefId uid) =
    (Parse 142, empty,
      s2par ("Invalid id " ++ ishow uid))
getErrorText (ESVPInvalidDefIdKeyword uid) =
    (Parse 143, empty,
      s2par ("Cannot define macro " ++ ishow uid ++ " as it is a keyword"))
getErrorText (ESVPRepeatedParamLabel uid) =
    (Parse 144, empty,
      s2par ("Repeated parameter label in " ++ ishow uid))
getErrorText (ESVPUndefinedId uid) =
    (Parse 145, empty,
      s2par ("Preprocessor macro " ++ ishow uid ++ " is not defined"))
getErrorText (ESVPWrongNumParams uid expected_num found_num) =
    (Parse 146, empty,
      s2par ("Error at `" ++ uid ++ ": Incorrect number of parameters: " ++
             "Expected " ++ show expected_num ++
             ", found " ++ show found_num ++ "."))
getErrorText (ESVPUnmatchedEndIf) =
    (Parse 147, empty,
      s2par ("Compiler directive `endif found but no earlier matching `ifdef"))
getErrorText (ESVPNoImportDelimiter) =
    (Parse 148, empty,
      s2par ("Expected \'\"\' or \'<\' after `include"))
getErrorText (ENoProvidedInterface) =
    (Parse 149, empty, s2par "No arg bound to interface provided by this instantiation")
getErrorText (EBadSpecialArgs) =
    (Parse 150, empty, s2par "Args like clocked_by not allowed in curried applications")
getErrorText (EForeignModOutputOrEnable method_name) =
    (Parse 151, empty, s2par ("Imported method " ++ method_name ++
                              " must have at least one of an output or enable signal (and may have both)."))
getErrorText (EDuplicateClocks clk_name) =
    (Parse 152, empty,
     s2par ("import BVI module contains duplicate clock declarations for " ++
            quote clk_name))
getErrorText (EScheduleUnrelatedClocks) =
    (Parse 153, empty, s2par "schedule specification involves unrelated clocks")
getErrorText (EInvalidMethod) =
    (Parse 154, empty, s2par "not a method (or possibly () missing from its definition)")
getErrorText (EBadAttributeName name loc allowed) =
    (Parse 155, empty,
     s2par ("Attribute " ++ quote name ++ " is not allowed on " ++ loc ++ ". "
          ++ "Allowable attributes are:" ) <+>
     quoteStrList allowed <> text "."
    )
getErrorText (EMultipleAttribute  name) =
    (Parse 156, empty, s2par ("Multiple " ++ quote name ++ " attributes are not supported."))
getErrorText (EBadPortRenameAttributeString attrname str) =
    (Parse 157, empty, s2par ("An invalid string " ++ doubleQuote str ++ " was used for the " ++ attrname ++ " attribute. " ++
                              "Attribute strings may not contain spaces or be empty in some cases." ))
getErrorText (EDuplicatePortRenameAttribute attrname method) =
    (Parse 158, empty, s2par ("A duplicate " ++ quote attrname ++ " attribute was found for the method or interface " ++
                              quote method ++ "." ))
getErrorText (EAttributeArgNotAllowed name) =
    (Parse 159, empty, s2par ("Attribute " ++ quote name ++ " does not support an argument in this context." ))
-- Removed Parse 160, EActionSelfSB has been reclassified as Type 94
getErrorText (EForbiddenDeclaration context) =
    (Parse 161, empty, s2par ("declarations forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenRepeat context) =
    (Parse 162, empty, s2par ("repeat construct forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenBreak context) =
    (Parse 163, empty, s2par ("break statement forbidden in " ++ context ++ " context"))
getErrorText (EForbiddenExpr typ  context) =
    (Parse 164, empty, s2par (typ ++ " statement forbidden in " ++ context ++ " context"))
getErrorText (EAttribsRepeat) =
    (Parse 165, empty, s2par "Attributes not allowed for repeat-statement")
getErrorText (EAttribsBreak) =
    (Parse 166, empty, s2par "Attributes not allowed for break statement")
getErrorText (EAttribsExpr typ) =
    (Parse 167, empty, s2par ("Attributes not allowed for " ++ typ ++ " statement"))
getErrorText (EForbiddenForeignFunction context) =
    (Parse 168, empty, s2par ("Foreign functions forbidden in " ++ context ++ " context"))
getErrorText (EAttribsForeignFunction) =
    (Parse 169, empty, s2par "Attributes not allowed for foreign functions")
getErrorText (EEmptyEnum) =
    (Parse 170, empty, s2par "Empty enumeration type")
getErrorText (EUniqueInst) =
    (Parse 171, empty, s2par "Only one instance name allowed")
getErrorText (WBVIActionMethodNoClock src_ids) =
    (Parse 172, empty,
     let hdr = s2par "Action methods clocked by no_clock are unusable:"
         showId (i,pos) = s2par (quote i ++ " at " ++ prPosition pos)
     in  hdr $+$
         nest 2 (vcat (map showId src_ids)))
getErrorText (EDuplicateResets rst_name) =
    (Parse 173, empty,
     s2par ("import BVI module contains duplicate reset declarations for " ++
            quote rst_name))
getErrorText (EReservedClock clk_name) =
    (Parse 174, empty,
     s2par (quote clk_name ++
            " is a reserved clock name and cannot be redeclared"))
getErrorText (EReservedReset rst_name) =
    (Parse 175, empty,
     s2par (quote rst_name ++
            " is a reserved reset name and cannot be redeclared"))
getErrorText (EObsolete i_type i msg) =
    (Parse 176, empty,
     s2par ("The " ++ i_type ++ " " ++ ishow i ++
            " is no longer supported.  " ++ msg))
getErrorText (EEmptyPrefixNoPortName s)
  | s == "default_clock" =
    (Parse 177, empty, s2par ("The default clock must be given a name if no prefix is used.  Either remove the empty clock_prefix/gate_prefix, use default_clock_osc/default_clock_gate to provide a port name, or use no_default_clock to remove the port entirely."))
  | s == "default_reset" =
    (Parse 177, empty, s2par ("The default reset must be given a name if no prefix is used.  Either remove the empty reset_prefix, use default_reset to provide a port name, or use no_default_reset to remove the port entirely."))
  | otherwise =
    (Parse 177, empty, s2par (s ++ " must be given a name if no prefix is used."))
getErrorText (EConflictingGateAttr s) =
    (Parse 178, empty, s2par ("Conflicting gate requirements on clock " ++ s))
getErrorText (WUnusedPrefix kind s) =
    (Parse 179, empty, s2par ("The " ++ kind ++ " prefix " ++ quote s ++ " is never used"))
getErrorText (WGateAllClocksIgnored) =
    (Parse 180, empty, s2par ("The gate_all_clocks attribute was given but the gate port was also removed from every clock."))
getErrorText (EAttributeOnWrongArgType attr_name arg_name reason) =
    (Parse 181, empty, s2par ("The " ++ attr_name ++ " attribute cannot be applied to module argument " ++ arg_name ++ " because it is " ++ reason ++ "."))
getErrorText (EAttributeNoSuchArg attr_name bogus_arg) =
    (Parse 182, empty, s2par ("The module argument " ++ quote bogus_arg ++
                              " named in the " ++ attr_name ++
                              " attribute does not exist."))
getErrorText (EPortsSameName clashing_ports) =
    (Parse 183, empty, s2par ("The names of these ports clash: ") $$
                       nest 2 (sepList (map showPort clashing_ports) comma))
  where showPort (n,p,a) = text (n ++ " from argument " ++ a ++ " at ") <>
                           text (prPosition p)
getErrorText (EPortKeywordClash port_name) =
    (Parse 184, empty, s2par ("The port name " ++ quote port_name ++
                              " clashes with a Verilog keyword."))
getErrorText (EPortNotValidIdent port_name) =
    (Parse 185, empty, s2par ("The port name " ++ quote port_name ++
        " is not an accepted Verilog identifier.  It must contain only " ++
        "letters, digits, $ and _, but cannot begin with $ or a digit."))
getErrorText (EConflictingSplitAttributes) =
    (Parse 186, empty, s2par ("Conflicting split and nosplit attributes"))
getErrorText (ESplitAttributeHasANumberThatIsNotUnity att _) =
  -- second parameter is the "wrong" number; ignoring it for now.
    (Parse 187, empty, s2par ("The attribute " ++ quote att ++
                              " may be only assigned the value 1."))
getErrorText (EExpressionStatementContext) =
    (Parse 188, empty, s2par ("Expression context not allowed here"))
getErrorText (ESplitAttrUpd split vars) =
    let attr = if split then "split" else "nosplit" in
    (Parse 189, empty, s2par ("The " ++ attr ++ " attribute is not permitted on any statement that updates free variables.") <+>
                       s2par ("Updated variables: " ++ unwordsAnd vars))
getErrorText (ESplitAttrBinding split) =
    let attr = if split then "split" else "nosplit" in
    (Parse 190, empty, s2par ("The " ++ attr ++ " attribute is not permitted on a declaration or binding statement."))
getErrorText (ESplitAttrReturn split)  =
    let attr = if split then "split" else "nosplit" in
    (Parse 191, empty, s2par ("The " ++ attr ++ " attribute is not permitted on a return statement."))
getErrorText (ESplitAttrNonActionCtx split)  =
    let attr = if split then "split" else "nosplit" in
    (Parse 192, empty, s2par ("The " ++ attr ++ " attribute is not permitted in a non-action context."))
-- Removed Parse 193 ESplitAttrActionValue, now that we allow splitting actionvalues
getErrorText (EBVIInputOverlap port) =
    (Parse 194, empty, s2par ("The foreign module input " ++ port ++ " is not unique."))
getErrorText (EBVIInputOutputOverlap port) =
    (Parse 195, empty, s2par ("The foreign module port " ++ port ++ " is used as an input and an output."))
getErrorText (EClockedByBadName bad_name valid_names) =
    (Parse 196, empty,
     s2par ("Module arguments can only be clocked by input clocks. " ++
            "The attribute value " ++ quote bad_name ++
            " is not recognized as an input clock name.  " ++
            "The following are valid options:") $$
     nest 2 (sepList (map text valid_names) comma))
getErrorText (EBVIMultipleOpts opt) =
    (Parse 197, empty, s2par ("Multiple " ++ quote opt ++ " clauses"))
getErrorText (EResetByBadName bad_name valid_names) =
    (Parse 198, empty,
     s2par ("Module arguments can only be reset by input resets. " ++
            "The attribute value " ++ quote bad_name ++
            " is not recognized as an input reset name.  " ++
            "The following are valid options:") $$
     nest 2 (sepList (map text valid_names) comma))
getErrorText (EMixedLitInNonPatCase num) =
    (Parse 199, empty,
     s2par ("Numeric literals with \'?\' are not supported in ordinary " ++
            "case statements: " ++ quote num ++ ".  " ++
            "Use a pattern-matching case statement."))
getErrorText (WNoSchedulingAnnotation ms1 op ms2) =
    (Parse 200, empty,
     fsep $ [text ("No scheduling annotation given between " ++ str_ms1),
             (pparen manyMs1 (commaSep ms1')), text "and",
             text str_ms2, (pparen manyMs2 (commaSep ms2')),
             text ("Assuming " ++ op ++ ".")])
  where manyMs1 = length ms1 > 1
        str_ms1 = if manyMs1 then "methods" else "method"
        manyMs2 = length ms2 > 1
        str_ms2 = if manyMs2 then "methods" else "method"
        ms1' = map (text . quote) ms1
        ms2' = map (text . quote) ms2
getErrorText (EBVIDuplicateSchedule pos op as bs) =
    (Parse 201, empty,
     s2par ("Schedule specification overlaps with previous specification " ++
            "at " ++ prPosition pos) $+$
     nest 2 (fsep [text "(" <> sepList (map text as) comma <> text ")",
                   text op,
                   text "(" <> sepList (map text bs) comma <> text ")"]))
getErrorText (EAttribsBVI) =
    (Parse 202, empty, s2par "Attributes not allowed for BVI statements")
getErrorText (EAttribsCase) =
    (Parse 203, empty, s2par "Attributes not allowed for case-statement")
getErrorText (EAttribsSequence) =
    (Parse 204, empty, s2par "Attributes not allowed for sequence block")
getErrorText (EAttribsProperty) =
    (Parse 205, empty, s2par "Attributes not allowed for property block")
getErrorText (EAttribsAssert) =
    (Parse 206, empty, s2par "Attributes not allowed for assert statement")
getErrorText (EAttribsExpect) =
    (Parse 207, empty, s2par "Attributes not allowed for expect statement")
getErrorText (EAttribsAssume) =
    (Parse 208, empty, s2par "Attributes not allowed for assume statement")
getErrorText (EAttribsCover) =
    (Parse 209, empty, s2par "Attributes not allowed for cover statement")
getErrorText (ECPPDirective) =
    (Parse 210, empty, s2par "Unexpected C preprocessor directive found. (Perhaps you need to specify the -cpp flag?)")
getErrorText (EBadMethodConflictOpList) =
    (Parse 211, empty,
      s2par ("This scheduling operator expects a single list of names"))
-- Removed: Parse 212
getErrorText (EScheduleNoClock) =
    (Parse 213, empty,
     s2par "schedule specification involves methods with no clocks")
getErrorText (EDuplicateIfcField field) =
    (Parse 214, empty,
     s2par ("import BVI module contains duplicate declarations for " ++
            quote field))
getErrorText (EMissingFunctionBody) =
    (Parse 215, empty,
     s2par "function definition with no body")
getErrorText (WPerhapsBadMethodName name) =
    (Parse 216, empty,
     s2par ("import BVI module declares " ++
            (quote name) ++
            " as a method name, which is maybe not what you intended."))
getErrorText (ESVPNoClosingParen cntx) =
    (Parse 217, empty,
      s2par ("missing closing paren for " ++ cntx))
getErrorText (EUnsupportedCaseStmt context) =
    (Parse 218, empty,
     s2par ("Case-statements are not supported in " ++ context ++
            " context.  Case-statements as Action are allowed if enclosed " ++
            "in an " ++ quote "action..endaction" ++ " block."))
getErrorText (EMultipleAssertionLabels) =
    (Parse 219, empty,
     s2par "assertions cannot have multiple names:")
getErrorText (ESequenceBind) =
    (Parse 220, empty,
     s2par ("Assignment with " ++ quote "<-" ++ " in sequence context " ++
            "is only allowed with " ++ quote "callServer" ++ ".  If an " ++
            "action context is desired, enclose the statement in an " ++
            quote "action..endaction" ++ " block."))

getErrorText (WTypesIgnored ctx) =
    (Parse 221, empty,
     s2par ("Partial type information for this " ++ ctx ++ " is being " ++
            "ignored.  At the moment, only full type declarations are " ++
            "supported.  If a type is missing for the return value or " ++
            "any of the arguments, then all types are ignored."))

getErrorText (ESVPNoId kw) =
    (Parse 222, empty,
     s2par ("missing macro identifier after " ++ quote kw))

getErrorText (WUnusedDef i) =
    (Parse 223, empty,
     s2par ("Definition of " ++ quote i ++ " is not used."))
getErrorText ENotUTF8 =
    (Parse 224, empty, s2par "File encoding is not UTF-8")

-- Type check and elaboration errors

getErrorText (ECannotDerive s) =
    (Type 0, empty, s2par ("Illegal deriving: " ++ s))
getErrorText (EDeriveCtx s) =
    (Type 1, empty, s2par ("Deriving failed because there is no instance " ++ ishow s))

getErrorText (EUndefinedTask c) =
    (Type 2, empty, s2par ("Unsupported system task " ++ ishow c))
getErrorText (EUnboundCon c maybeSuggest) =
    (Type 3, empty,
     let intro_msg = "Unbound constructor " ++ ishow c
         msg = case maybeSuggest of
           Nothing -> intro_msg
           Just fname -> intro_msg ++ ".  Perhaps " ++ quote fname ++ " is missing?"
     in s2par msg)
getErrorText (EUnboundVar c) =
    (Type 4, empty, s2par ("Unbound variable " ++ ishow c))
getErrorText (EUnboundField c) =
    (Type 5, empty,
     s2par ("Unbound field " ++ ishow c ++ ".  " ++
            "Perhaps the name was mis-spelled " ++
            "or the type has not been imported."))
getErrorText (EUnboundClCon c) =
    (Type 6, empty, s2par ("Unbound class " ++ ishow c))
getErrorText (EUnboundTyCon c) =
    (Type 7, empty, s2par ("Unbound type constructor " ++ ishow c))
getErrorText (EUnboundTyVar c) =
    (Type 8, empty, s2par ("Unbound type variable " ++ ishow c))
getErrorText (EUnboundExport c exclude) =
    (Type 9, empty,
     s2par (item ++ ishow c ++ " is not defined"))
  where item
          | exclude = "Export-excluded identifier "
          | otherwise = "Exported identifier "
getErrorText (ETypeNotExported c defs) =
    (Type 10, empty, s2par ("Missing export for type " ++ ishow c) $$
                     vcat (map showdef defs))
  where
    showdef (name, pos) =
        s2par ("used in the definition of " ++ ishow name ++
               " at " ++ prPosition pos)
getErrorText (EMultipleDecl name prevPos) =
    (Type 11, empty, s2par ("Declaration of " ++ ishow name ++
                            " conflicts with previous declaration at " ++
                            prPosition prevPos))
getErrorText (EForeignNotBit i) =
    (Type 12, empty, s2par ("Foreign function has non-Bit argument/result: " ++ ishow i))
getErrorText (EPartialTypeApp i) =
    (Type 13, empty, s2par ("Partially applied type synonym " ++ ishow i))
getErrorText (ENotStructId c) =
    (Type 14, empty, s2par ("Identifier is not a struct name " ++ ishow c))
getErrorText (ENotStructUpd e) =
    (Type 15, empty, s2par ("Expression " ++ e ++ " is not an updateable structure."))
getErrorText (ENotField c f) =
    (Type 16, empty,
     s2par ("Field " ++ ishow f ++ " is not in the type " ++ ishow c ++
            " which was derived for this expression."))
getErrorText (EDupField f) =
    (Type 17, empty, s2par ("Field " ++ ishow f ++ " defined more than once"))
getErrorText (EFieldAmb ts f) =
    (Type 18, empty,
     s2par ("The field " ++ ishow f ++ " is a member of multiple structs " ++
            "or interfaces, and there was not enough type information to " ++
            "decide which one is being referred to.  Consider adding more " ++
            "explicit types, to help the compiler choose.  The following " ++
            "structs/interfaces have a field named " ++ ishow f ++ ":") $$
     nest 2 (sepList (map text ts) comma))
getErrorText (EConstrAmb t f) =
    (Type 19, empty, s2par ("Constructor " ++ ishow f ++ " is not disambiguated by type " ++ ishow t))
getErrorText (EUnify e t1 t2) =
    (Type 20, empty,
     s2par "Type error at:" $$
     nest 2 (text e) $$
     s2par "Expected type:" $$
     nest 2 (text t2) $$
     s2par "Inferred type:" $$
     nest 2 (text t1))
getErrorText (EUnifyKind t k_inferred k_expected) =
    (Type 21, empty,
     s2par "Kind error at:" $$
     nest 2 (text t) $$
     s2par "Expected kind:" $$
     nest 2 (text k_expected) $$
     s2par "Inferred kind:" $$
     nest 2 (text k_inferred))
getErrorText (ENumKindArg) =
    (Type 22, empty, s2par "Numeric types do not take arguments.")
getErrorText (ETypeNoArg i) =
    (Type 23, empty, s2par ("The type " ++ ishow i ++ " does not take an argument."))
getErrorText (ETypeTooManyArgs i) =
    (Type 24, empty, s2par ("The type " ++ ishow i ++ " is applied to too many arguments."))
getErrorText (ETypeTooFewArgs i) =
    (Type 25, empty, s2par ("The type " ++ ishow i ++ " is applied to too few arguments."))
getErrorText (EKindStarForNum i) =
    (Type 26, empty, s2par ("The value type " ++ ishow i ++ " was found where a numeric type was expected."))
getErrorText (EKindNumForStar i) =
    (Type 27, empty, s2par ("The numeric type " ++ ishow i ++ " was found where a value type was expected."))
getErrorText (EKindArg s) =
    (Type 28, empty, s2par ("Wrong number of arguments to class: " ++ s))
getErrorText (ETooGeneral sc sc') =
    (Type 29, empty, s2par "Signature mismatch (given too general):" $$ text "given:" $$ text sc $$ text "deduced:" $$ text sc')

getErrorText (EWeakContext t qs rps type_var_positions) =
    (Type 30, empty,
     let ctx = if isClassic() then "context" else "proviso"
         qs_ctx = ctx ++ if (length qs == 1) then "" else "s"
         adtl = if (null qs) then "" else "additional "
         mk_r_msg (r,poss,reduced_rs) =
           let pos_msg =
                   s2par "Introduced at the following locations:" $$
                   -- noticed that some positions repeat, so use "nub"
                   nest 2 (vcat (map (text . prPosition) (nub poss)))
               reduced_msg =
                   s2par ("The " ++ ctx ++ " could also be deduced from " ++
                          "the following information:") $$
                   nest 2 (vcatList (map text reduced_rs) comma)
           in  s2par r $$
               nest 2 ((if (null poss) then empty else pos_msg) $$
                       (if (null reduced_rs) then empty else reduced_msg))
         mk_tv_msg (var, pos) = (text "\"" <> text var <> text "\"" <+>
                                 text "at" <+> text (prPosition pos))
     in  s2par ("The " ++ ctx ++ "s for this expression are too general.") $$
         s2par "Given type:" $$
         nest 2 (s2par t) $$
         (if (null qs)
          then empty
          else s2par ("With the following " ++ qs_ctx ++ ":") $$
               nest 2 (vcat (map s2par qs))
          ) $$
         s2par ("The following " ++ adtl ++ ctx ++ "s are needed:") $$
         nest 2 (vcat (map mk_r_msg rps)) $$
         (if null type_var_positions then empty else
          (s2par ("The type variables are from the following positions:") $$
           nest 2 (vcat (map mk_tv_msg type_var_positions))))
    )

getErrorText (EContextReduction context positions vps) =
    (Type 31, empty,
     let ctx = if isClassic() then "context" else "proviso"
         intro_msg =
           s2par ("The " ++ ctx ++ "s for this expression could not be resolved " ++
                  "because there are no instances of the form:") $$
           nest 2 (text context)
         pos_msg =
           s2par ("The " ++ ctx ++ " was implied by expressions at " ++
                  "the following positions:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
{-
     -- The type variables don't seem to offer new position info
         mk_vp_msg (v,pos) = s2par ("The type variable " ++ ishow v ++
                                    " was introduced at " ++ prPosition pos)
     in
         if (length(vps) == 0)
         then msg
         else msg $$ (vcat (map mk_vp_msg vps))
-}
     in  msg
    )

-- Type 32 was EContextReductionVar until it merged with EContextReduction
-- sufficiently long ago that we can reuse the number now
getErrorText (EContextReductionReduces context reduced_contexts positions vps) =
    (Type 32, empty,
     let ctx = if isClassic() then "context" else "proviso"
         intro_msg =
           s2par ("This expression requires the following " ++ ctx ++
                  " which could not be resolved:") $$
           nest 2 (text context)
         pos_msg =
           s2par ("The " ++ ctx ++ " was implied by expressions at " ++
                  "the following positions:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         reduce_msg =
           let p = if length reduced_contexts > 1 then "s" else ""
               be = if length reduced_contexts > 1 then "are" else "is"
           in
           s2par ("An instance for this " ++ ctx ++ " exists, " ++
                  "but it depends on the following " ++ ctx ++ p ++
                  " for which there " ++ be ++ " no instance" ++ p ++ ":") $$
           nest 2 (vcatList (map text reduced_contexts) comma)
         msg = if null positions
               then intro_msg            $$ reduce_msg
               else intro_msg $$ pos_msg $$ reduce_msg
     in  msg
    )

getErrorText (EAmbiguous ambiguous_var_infos) =
    (Type 33, empty,
     let mkVarMsg (var, var_pos, use_expls) =
             s2par ("An ambiguous type was introduced at " ++
                    prPosition var_pos) $$
             s2par ("This type resulted from:") $$
             nest 2 (vcat use_expls)
         msgs = map mkVarMsg ambiguous_var_infos
     in
         s2par ("There is not enough explicit type information to deduce " ++
                "the types of all expressions.  Consider adding more type " ++
                "declarations to help resolve this ambiguity.") $$
         -- since we don't print the name of the variables
         -- there can be duplicate messages when multiple variables are
         -- introduced at the same place, so use "nub" on the message
         -- (not on the variable list)
         nest 2 (vcat (nub msgs))
    )
getErrorText (EWrongArity) =
    (Type 34, empty, s2par "Clause has wrong number of arguments")
getErrorText (EUnknownSize) =
    (Type 35, empty, s2par "Bit vector of unknown size introduced near this location." $$
                     s2par ("Please remove unnecessary extensions, truncations and concatenations " ++
                            "and/or provide more type information to resolve this ambiguity."))
getErrorText (ENotExpr) =
    (Type 36, empty, s2par ("Last statement in a " ++ quote "do" ++ " must be an expression"))
getErrorText (ELocalRec is) =
    (Type 37, empty, s2par ("Local recursion without signature not allowed: " ++ (unwordsAnd (map ishow is))))
getErrorText (ENotAnInterface) =
    (Type 38, empty, s2par "Not of interface type")
getErrorText (ENotModule i) =
    (Type 39, empty, s2par ("Not of Module type: " ++ ishow i))
getErrorText (EPolyField) =
    (Type 40, empty, s2par "Polymorphic field not allowed in code generation.")
getErrorText (ENotKNum t) =
    (Type 41, empty, s2par ("Only size polymorphism allowed in code generation: " ++ t))
getErrorText (EBadGenArg i) =
    (Type 42, empty, s2par ("Bad argument in code generation: " ++ ishow i))
getErrorText (EBadIfcType mod msg) =
    (Type 43, empty,
     s2par ("Cannot synthesize " ++ quote mod ++ ": " ++ msg))
getErrorText (ENoTypeSign e) =
    (Type 44, empty, s2par ("Missing or bad type signature for a module: " ++ e))
getErrorText (EStmtContext c) =
    (Type 45, empty, s2par ("Binding has context: " ++ c))
getErrorText (EBadMatch p) =
    (Type 46, empty,
     let kase = if isClassic() then "a case expression" else "a case statement"
     in  s2par ("Only matching of structs and tuples is supported " ++
                "in this context.") $$
         s2par ("The following pattern is not supported:") $$
         nest 2 (text p) $$
         s2par ("Consider matching this pattern with " ++ kase ++ " instead.")
    )
getErrorText (EBitSel n k m e) =
    (Type 47, empty, s2par ("Bit selection out of range: " ++ n ++ " + " ++ k ++ " > " ++ m ++ " in") $$ text e)
getErrorText EMultipleInterfaces =
    (Type 48, empty, s2par "Multiple interfaces")
getErrorText (EValueOf s) =
    (Type 49, empty, s2par ("Cannot take valueOf " ++ ishow s ++ " (symbol might not be in scope)"))

getErrorText (EBadVeriType t) =
    (Type 50, empty, s2par ("Bad type in module for code-generation: " ++ t))
getErrorText (EInvalidLiteral tid s il) =
    (Type 51, empty,
     s2par ("Literal " ++ il ++ " is not a valid " ++ tid ++ "#(" ++ show s ++ ")."))

-- Error 52 is really a generation error bug 500

-- Error 53 (EPrimExtractTooLarge) was most recently used to indicate when
-- an extracted size was larger than expected by the context, though the
-- message text suggests that it might have originally been intended for when
-- the extracted size was larger than the source vector itself.  In any case,
-- all of these static index failures are now detected by source code (in the
-- Prelude) and reported with primError.

getErrorText (WMissingField s) =
    (Type 54, empty, s2par ("Field not defined: " ++ ishow s))

getErrorText (EForeignModBadArgType t mod pos) =
    (Type 55, empty, s2par ("Foreign module method has non-Bit argument: " ++ t) $$ s2par ("Used by module " ++ quote mod ++ " at " ++ pos))
getErrorText (EForeignModBadResType t mod pos) =
    (Type 56, empty, s2par ("Foreign module method has non-Bit/Action result: " ++ t) $$ s2par ("Used by module " ++ quote mod ++ " at " ++ pos))
getErrorText (EForeignModTooManyPorts method) =
    (Type 57, empty, s2par ("The method " ++ ishow method ++ " is connected to too many foreign module ports."))
getErrorText (EForeignModTooFewPorts method) =
    (Type 58, empty, s2par ("The method " ++ ishow method ++ " is connected to too few foreign module ports."))
-- Removed Type 59 EBindDummyId b/c "_" variable name is now valid in BSV
getErrorText (ECtxRedWrongBitSize t tsz sz2 positions) =
    (Type 60, empty,
     let intro_msg =
           s2par ("Expression could not be compiled because of a " ++
                  "bit-size mismatch.") $$
           s2par ("The type:") $$
           nest 2 (text t) $$
           s2par ("has a bit size of " ++ itos tsz ++ " " ++
                  "but is either being used as or created by a bit vector " ++
                  "of size " ++ itos sz2 ++ ".")
         pos_msg =
           s2par ("The mismatch occurs in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if (length(positions) == 0)
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedBitwiseBool positions) =
    (Type 61, empty,
     let intro_msg =
           s2par ("Bitwise operators are not defined for Boolean values. " ++
                  "Consider using the Boolean operators && and || instead.")
         pos_msg =
           s2par ("Bitwise operators were used on Boolean values " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedBitwise t positions) =
    (Type 62, empty,
     let intro_msg =
           s2par ("Bitwise operators are not defined for the type:") $$
           nest 2 (text t) $$
           s2par ("Consider converting the value to bits or defining the " ++
                  "bitwise operators for this type.")
         pos_msg =
           s2par ("Bitwise operators were used on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedBitExtendBadSizes sz1 sz2 positions) =
    (Type 63, empty,
     let intro_msg =
           s2par ("A vector of size " ++ (itos sz1) ++ " " ++
                  "is being extended to size " ++ (itos sz2) ++ " " ++
                  "or a vector of size " ++ (itos sz2) ++ " " ++
                  "is being truncated to size " ++ (itos sz1) ++ ", " ++
                  "which is not allowed since " ++ (itos sz1) ++ " > " ++
                  (itos sz2) ++ ".")
         pos_msg =
           s2par ("The extend or truncate occurs " ++
                  "in or near the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedBitExtendBadType t positions) =
    (Type 64, empty,
     let intro_msg =
           s2par ("The bit-vector operations extend and truncate " ++
                  "are not defined for type:") $$
           nest 2 (text t) $$
           s2par ("Consider converting the type to bits first.")
         pos_msg =
           s2par ("The extend or truncate occurs " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )

getErrorText (EWeakCtxBitExtendNeedsAddCtx t qs addctx reduced_rs positions) =
    (Type 65, empty,
     let ctx = if isClassic() then "context" else "proviso"
         adtl = if (null qs) then "" else "additional "
         intro_msg =
             s2par ("The " ++ ctx ++ "s for this expression are " ++
                    "too general.") $$
             s2par "Given type:" $$
             nest 2 (s2par t) $$
             (if (null qs)
              then empty
              else s2par "With the following provisos:" $$
                   nest 2 (vcat (map s2par qs))
              ) $$
             s2par ("The following " ++ adtl ++ ctx ++ " is needed:") $$
             nest 2 (s2par addctx) $$
             s2par ("This " ++ ctx ++ " was introduced by an " ++
                    "extend or truncate operation, which requires that " ++
                    "the extended size be larger.")
         pos_msg =
           if null positions
           then empty
           else s2par ("The extend or truncate occurs " ++
                       "in or at the following locations:") $$
                -- use "nub" out of paranoia (saw repeats with EWeakContext)
                nest 2 (vcat (map (text . prPosition) (nub positions)))
         reduced_msg =
           if (null reduced_rs)
           then empty
           else s2par ("The " ++ ctx ++ " could also be deduced from " ++
                       "the following information:") $$
                nest 2 (vcatList (map text reduced_rs) comma)
         msg = intro_msg $$ pos_msg $$ reduced_msg
     in msg
    )

getErrorText (EAssignNotReg t) =
    (Type 66, empty,
         s2par ("The left-hand side of an assignment must be a " ++
                "register or interface type.  The expression at this location has type:") $$
         nest 2 (s2par t))

-- Removed Type 67 EAssignListReg. Made obsolete by typeclass PrimUpdateable
-- and the special case handling of provisos errors containing it.

getErrorText (EBoundTyVarKindMismatch tyvar_id kind1 kind1_pos kind2 kind2_pos) =
    (Type 68, empty,
     s2par ("Kind mismatch on bound type variable " ++ quote tyvar_id ++ ".") $+$
     s2par ("The variable has kind " ++ quote kind1 ++ " at position:") $+$
     nest 2 (text (prPosition kind1_pos)) $+$
     s2par ("The variable has kind " ++ quote kind2 ++ " at position:") $+$
     nest 2 (text (prPosition kind2_pos)))
getErrorText (EOverlappingTagEncoding type_name value guilty_tags) =
    let tag_conflicts = [s2par ("    tag " ++ ishow tag ++ " introduced at " ++
                                prPosition pos) | (pos, tag) <- guilty_tags]
    in (Type 69, empty, s2par ("Multiple tags in type \"" ++
                                 type_name ++ "\" encode to " ++
                                 show value ++ ":") $$
        vcat tag_conflicts)
getErrorText (ECtxRedNotSelectable t positions) =
    (Type 70, empty,
     let intro_msg =
           s2par ("Selection with [] is not defined for the type:") $$
           nest 2 (text t)
         pos_msg =
           s2par ("Selection was performed on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedWrongSelectionResult arr expect_val found_val positions) =
    (Type 71, empty,
     let intro_msg =
           s2par ("Selection with [] from a value of type:") $$
           nest 2 (text arr) $$
           s2par ("should result in a value of type:") $$
           nest 2 (text expect_val) $$
           s2par ("Instead, the following result type was found:") $$
           nest 2 (text found_val)
         pos_msg =
           s2par ("Selection was performed on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedBadSelectionIndex found_idx positions) =
    (Type 72, empty,
     let intro_msg =
           s2par ("Selection with [] is not possible with an index value of type:") $$
           nest 2 (text found_idx) $$
           s2par ("Instead, use a valid indexing type (e.g. Integer or Bit#())")
         pos_msg =
           s2par ("Selection was performed with this index type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )

-- Removed Type 73, EWeakCtxPrimSelectableNeedsPrimIndexCtx. PrimIndex
-- is no longer a superclass of PrimSelectable but is just part of the
-- member function's signature

getErrorText (ECtxRedBitReduce t positions) =
    (Type 74, empty,
     let intro_msg =
           s2par ("Bit reduction operators are not defined for the type:") $$
           nest 2 (text t) $$
           s2par ("Consider converting the value to bits or defining the " ++
                  "bitwise operators for this type.")
         pos_msg =
           s2par ("Bit reduction operators were used on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )

getErrorText (EForeignModMissingValuePort desc mod meth) =
    (Type 75, empty,
     s2par ("Missing return value port for " ++ desc ++
            " method " ++ ishow meth ++ " in BVI import for module " ++
            ishow mod ++ "."))
getErrorText (EForeignModMissingEnablePort desc mod meth) =
    (Type 76, empty,
     s2par ("Missing enable port for " ++ desc ++
            " method " ++ ishow meth ++ " in BVI import for module " ++
            ishow mod ++ "."))
getErrorText (EForeignModUnexpectedValuePort desc mod meth) =
    (Type 77, empty,
     s2par ("Unexpected return value port for " ++ desc ++
            " method " ++ ishow meth ++ " in BVI import for module " ++
            ishow mod ++ "."))
getErrorText (EForeignModUnexpectedEnablePort desc mod meth) =
    (Type 78, empty,
     s2par ("Unexpected enable port for " ++ desc ++
            " method " ++ ishow meth ++ " in BVI import for module " ++
            ishow mod ++ "."))

getErrorText (EAmbiguousExplCtx amb_vars amb_preds base_type) =
    (Type 79, empty,
     let ctx = if isClassic() then "context" else "proviso"
     in  s2par ("The following type variables:") $$
         nest 2 (sepList amb_vars comma) $$
         s2par ("are not uniquely determined by the following " ++
                ctx ++ "s:") $$
         nest 2 (vcat amb_preds) $$
         s2par ("and do not appear in the base type:") $$
         nest 2 base_type $$
         s2par ("Rewrite the provisos so that there are no ambiguous " ++
                "variables.")
    )

getErrorText (EFuncMismatchResult e t1 t2 res1 res2) =
    (Type 80, empty,
     s2par "Type error at the use of the following function:" $$
     nest 2 (text e) $$
     s2par "The expected return type of the function:" $$
     nest 2 (text res2) $$
     s2par "The return type according to the use:" $$
     nest 2 (text res1))

getErrorText (EFuncMismatchNumArgs e t1 t2 n1 n2 maybe_startnum) =
    (Type 81, empty,
     s2par "Wrong number of arguments in the use of the following function:" $$
     nest 2 (text e) $$
     s2par ("The function expects " ++ show n1 ++
            " arguments but was used with " ++ show n2 ++ " arguments.") $$
     (case (maybe_startnum) of
          Nothing -> empty
          Just startnum ->
              s2par ("The first type mismatch occurs in argument " ++
                     show startnum ++ ".")
      ) $$
     text "" $$
     s2par "Expected type:" $$
     nest 2 (text t1) $$
     s2par "Inferred type:" $$
     nest 2 (text t2))

getErrorText (EFuncMismatchArgN e t1 t2 num argt1 argt2) =
    (Type 82, empty,
     s2par ("Type mismatch in argument " ++ show num ++
            " to the following function:") $$
     nest 2 (text e) $$
     s2par "The function expects an argument of type:" $$
     nest 2 (text argt1) $$
     s2par "But was used with a value of type:" $$
     nest 2 (text argt2) $$
     s2par "Expected type for the function:" $$
     nest 2 (text t1) $$
     s2par "Inferred type:" $$
     nest 2 (text t2))

getErrorText (EFuncMismatchNoArgsExpected e t1 t2) =
    (Type 83, empty,
     s2par ("The following expression does not expect arguments, " ++
            "but was used with arguments:") $$
     nest 2 (text e) $$
     s2par "The expected type is:" $$
     nest 2 (text t1) $$
     s2par "But it was used with the following type:" $$
     nest 2 (text t2))

getErrorText (EFuncMismatchArgsExpected e t1 t2 n) =
    (Type 84, empty,
     s2par ("The following function expects " ++ show n ++
            " arguments, but it was used without any arguments:") $$
     nest 2 (text e) $$
     s2par "The expected type is:" $$
     nest 2 (text t1) $$
     s2par "But it was used with the following type:" $$
     nest 2 (text t2))

-- Removed Type 85, ECtxRedSelectionIndexTooLong
-- Removed Type 86, EWeakCtxPrimIndexNeedsAddCtx
-- Both removed due to PrimIndex improvements. The PrimIndex instance for
-- Bit vector no longer has an Add context, because there's no longer an
-- arbitrary 32-bit limit applied to all indexing.

getErrorText (EForeignFuncStringRes) =
    (Type 87, empty,
     s2par ("The return type of foreign functions cannot be String.  " ++
            "Only types which can be packed to bit-vectors are allowed."))

getErrorText (EForeignFuncBadArgType pairs) =
    (Type 88, empty,
     let (badtypes, isPolys) = unzip $ pairs
         hdr = s2par ("The arguments to foreign functions must be of type " ++
                      "String or of types which can be packed to " ++
                      "bit-vectors.  The following types cannot be " ++
                      "converted to bits.") <+>
               if (any id isPolys)
                 then s2par ("Consider adding a Bits proviso for any " ++
                             "variable types.")
                 else empty
     in  hdr $$ nest 2 (vcat (map text badtypes)))

getErrorText (EForeignFuncBadResType badtype isPoly) =
    (Type 89, empty,
     let hdr = s2par ("The return value of a foreign functions must be of " ++
                      "a type which can be packed to a bit-vector.  " ++
                      "The following type cannot be converted to bits.") <+>
               if (isPoly)
                 then s2par ("Consider adding a Bits proviso.")
                 else empty
     in  hdr $$ nest 2 (text badtype))

-- Removed Type 90, EDeriveRecursive since recursive deriving of Bits
-- now causes an ERecursiveBits error at the type checking phase.

getErrorText (EForeignFuncDuplicates link_name src_ids) =
    (Type 91, empty,
     let hdr = s2par ("Cannot import a foreign function more than once.  " ++
                      "The function " ++ quote link_name ++
                      " was imported as the following BSV names:")
         showId (i,pos) = s2par (quote i ++ " at " ++ prPosition pos)
     in  hdr $+$
         nest 2 (vcat (map showId src_ids))
    )

getErrorText (EMissingFileArgument task typ place) =
    (Type 92, empty,
     s2par ("Verilog system task " ++ ishow task ++
            " expects a variable of type " ++ ishow typ ++
            " as its " ++ ishow place ++ " argument.")
    )

getErrorText (EMethodArgNameMismatch meth mismatches) =
    (Type 93, empty,
     let showMismatch (def_id, decl_id) =
             s2par (ishow def_id ++ " vs " ++ ishow decl_id)
     in  s2par ("The argument names in the definition of method " ++
                ishow meth ++ " do not match the names in the " ++
                "declaration of the interface:") $+$
         nest 2 (vcat (map showMismatch mismatches)))

getErrorText (EActionSelfSB methods) =
    (Type 94, empty,
     let intro = "An Action or ActionValue method cannot be SB with itself " ++
                 "(it must be SBR, CF or C)."
     in case methods of
          [m] -> s2par (intro ++ "  The SB annotation for " ++ quote m ++ " is not allowed.")
          _   -> s2par (intro ++ "  The SB annotation is illegal for these methods:") $$
                 nest 2 (vcat (map text methods))
    )

getErrorText (ECtxRedNotUpdateable t positions) =
    (Type 95, empty,
     let intro_msg =
           s2par ("Compile-time updates with [] and = are not defined for the type:") $$
           nest 2 (text t)
         pos_msg =
           s2par ("Updates were performed on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedWrongUpdateArg arr expect_val found_val positions) =
    (Type 96, empty,
     let intro_msg =
           s2par ("Compile-time updates with [] and = on a value of type:") $$
           nest 2 (text arr) $$
           s2par ("require an argument value of type:") $$
           nest 2 (text expect_val) $$
           s2par ("Instead, the following argument type was found:") $$
           nest 2 (text found_val)
         pos_msg =
           s2par ("Updates were performed on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )


getErrorText (ECtxRedNotWriteable t positions) =
    (Type 97, empty,
     let intro_msg =
           s2par ("Run-time writes with [] and <= are not defined for the type:") $$
           nest 2 (text t)
         pos_msg =
           s2par ("Writes were performed on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )
getErrorText (ECtxRedWrongWriteArg arr expect_val found_val positions) =
    (Type 98, empty,
     let intro_msg =
           s2par ("Run-time writes with [] and <= for a value of type:") $$
           nest 2 (text arr) $$
           s2par ("require an argument value of type:") $$
           nest 2 (text expect_val) $$
           s2par ("Instead, the following argument type was found:") $$
           nest 2 (text found_val)
         pos_msg =
           s2par ("Writes were performed on this type " ++
                  "in or at the following locations:") $$
           -- use "nub" out of paranoia (saw repeats with EWeakContext)
           nest 2 (vcat (map (text . prPosition) (nub positions)))
         msg = if null positions
               then intro_msg
               else intro_msg $$ pos_msg
     in msg
    )

getErrorText (EDuplicateInstance instance_head position) =
   (Type 99, empty,
    s2par ("Duplicate typeclass instances defined for " ++ instance_head ++
           "The previous instance was defined at " ++ ppReadable position ++
           "Please remove an applicable instance declaration or deriving request"))

getErrorText (EForeignModNotClockType f t mod mod_pos) =
    (Type 100, empty,
     s2par ("The interface field " ++ quote f ++
            " has type " ++ quote t ++
            " but is connected to an output clock in the foreign module " ++
            quote mod ++ " at " ++ mod_pos))
getErrorText (EForeignModNotResetType f t mod mod_pos) =
    (Type 101, empty,
     s2par ("The interface field " ++ quote f ++
            " has type " ++ quote t ++
            " but is connected to an output reset in the foreign module " ++
            quote mod ++ " at " ++ mod_pos))
getErrorText (EForeignModClockHasArgs f mod mod_pos) =
    (Type 102, empty,
     s2par ("Foreign module output clock cannot have arguments: " ++ f) $$
     s2par ("Used by module " ++ quote mod ++ " at " ++ mod_pos))
getErrorText (EForeignModResetHasArgs f mod mod_pos) =
    (Type 103, empty,
     s2par ("Foreign module output reset cannot have arguments: " ++ f) $$
     s2par ("Used by module " ++ quote mod ++ " at " ++ mod_pos))

getErrorText (EForeignModNotField ifc f) =
    -- we don't display "ifc" because it's the mangled generated ifc name
    (Type 104, empty, s2par ("The interface of this foreign module " ++
                             "does not have a field " ++ ishow f))
getErrorText (EForeignModMissingField f mod mod_pos) =
    (Type 105, empty, s2par ("The interface field " ++ ishow f ++
                             " is missing in the foreign module import " ++
                             quote mod ++ " at " ++ mod_pos))
getErrorText (ETypeSynRecursive names) =
    (Type 106, empty, s2par ("There are circular references among the following type synonyms: " ++
                             unwordsAnd names))
getErrorText (ECtxRedIsModule mod_type positions) =
    (Type 107, empty,
     let intro_msg =
           s2par ("The type " ++ quote mod_type ++ " is not a module.  " ++
                  "Perhaps you have used the wrong function in a module " ++
                  "instantiation, such as " ++ quote "map" ++ " vs " ++
                  quote "mapM" ++ ".")
         pos_msg =
           s2par ("Consider the modules at the following locations:") $$
           nest 2 (vcat (map (text . prPosition) (nub positions)))
     in  if null positions
         then intro_msg
         else intro_msg $$ pos_msg
    )
getErrorText (EModInstWrongArgs positions) =
    (Type 108, empty,
     let intro_msg =
           s2par ("Module instantiation has the wrong number of arguments.")
         pos_msg =
           s2par ("Consider the modules at the following locations:") $$
           nest 2 (vcat (map (text . prPosition) (nub positions)))
     in  if null positions
         then intro_msg
         else intro_msg $$ pos_msg
    )

getErrorText (ENoInlineAction func_name) =
    (Type 109, empty,
     s2par ("Action functions cannot be separately synthesized."))

getErrorText (ENoInlineContext func_name) =
    (Type 110, empty,
     let ctxs = if isClassic() then "contexts" else "provisos"
     in  s2par ("Functions with " ++ ctxs ++
                " cannot be separately synthesized."))

getErrorText (ENoInlinePolymorphic func_name) =
    (Type 111, empty,
     s2par ("Functions with type variables cannot by separately synthesized."))

getErrorText (ETypeStackOverflow) =
    (Type 112, empty,
         s2par "Stack overflow due to excessively deep recursion of types.")

getErrorText (ECtxRedIsModuleActionValue positions) =
    (Type 113, empty,
     let intro_msg =
           s2par ("Either an Action/ActionValue statement was used in " ++
                  "a module block or else a module instantiation was " ++
                  "used in an Action/ActionValue block.")
         pos_msg =
           s2par ("Consider the modules at the following locations:") $$
           nest 2 (vcat (map (text . prPosition) (nub positions)))
     in  if null positions
         then intro_msg
         else intro_msg $$ pos_msg
     )

-- Removed Type 114 ETypeFundepStackOverflow. TIMonad no longer keeps a
-- fundeps stack, since fundep handling became simpler by requiring fundeps
-- on classes to be fully specified.

getErrorText (ERecursiveBits bits s) =
    (Type 115, empty,
         s2par ("Recursive " ++ (quote bits)
                ++ " instance of " ++ (quote s)
                ++ " is forbidden."))

getErrorText (ETypeSuperStackOverflow) =
    (Type 116, empty,
         s2par ("Type inference context stack overflow occurred."
               ))

getErrorText (EUnboundPackage p) =
    (Type 117, empty,
     s2par ("The package " ++ ishow p ++ " has not been imported."))

getErrorText (EBadForeignIfcType t) =
    (Type 118, empty,
     s2par ("Cannot import a module with the type " ++ quote t ++ ".  " ++
            "It is not an interface or it has a polymorphic method."))
getErrorText (EForeignModNotInoutType f t mod mod_pos) =
    (Type 119, empty,
     s2par ("The interface field " ++ quote f ++
            " has type " ++ quote t ++
            " but is connected to an inout in the foreign module " ++
            quote mod ++ " at " ++ mod_pos))
getErrorText (EForeignModInoutHasArgs f mod mod_pos) =
    (Type 120, empty,
     s2par ("Foreign module inout cannot have arguments: " ++ f) $$
     s2par ("Used by module " ++ quote mod ++ " at " ++ mod_pos))
getErrorText (ETaskMismatchNumArgs e expected n) =
    (Type 121, empty,
     s2par "Wrong number of arguments for the system task:" $$
     nest 2 (text e) $$
     s2par ("The task expects " ++ expected ++
            " arguments but was used with " ++ show n ++ " arguments."))

getErrorText (EDuplicateExport c exclude) =
    (Type 122, empty, s2par ("Duplicate " ++ item ++ ishow c))
  where item = "export " ++ (if exclude then "hiding " else "")
getErrorText (EDuplicateDefInPackageExport pkg def) =
    (Type 123, empty,
     s2par ("Exported identifier " ++ ishow def ++
            " is already exported in package " ++ ishow pkg))

getErrorText (EClassFundepsNotFull cls vars fundeps) =
    (Type 124, empty,
     s2par ("Dependencies for typeclass " ++ quote cls ++
            " must mention all the following typeclass variables (as sources or targets): " ++
            intercalate ", " vars) $$
     text "The following dependencies are not full:" $$
       nest 2 (vcatList (map pDependency fundeps) empty))
  where pDependency (sources, targets) =
            commaSep (map text sources) <+> text "determines" <+> commaSep (map text targets)

-- Type 125 reserved for inconsistent fundeps (if we ever decide to have that error or warning)

getErrorText (WIncoherentMatch pred inst) =
    (Type 126, empty,
     s2par ("Proviso " ++ pred ++ " satisfied by incoherently matching the instance " ++ inst))

getErrorText (WOrphanInst inst) =
    (Type 127, empty,
     s2par ("Exporting orphan typeclass instance " ++ inst ++ ". " ++
            "The instance's typeclass as well as all of the instance's source type parameters " ++
            " are defined in other packages. This can lead to confusing and inconsistent " ++
            " instance resolution if the orphan instance is not imported everywhere it could be used."))

getErrorText (EBadInstanceOverlap inst1 inst2 position2) =
    (Type 128, empty,
     s2par ("Overlapping typeclass instances " ++ inst1 ++ " and " ++ inst2 ++
             "(defined at " ++ ppReadable position2 ++ ") cannot be ordered " ++
             "from most-specific to least-specific, so they cannot support " ++
             "predictable instance-resolution. Please resolve this by changing one " ++
             "or both of the instances."))

getErrorText (EBadExtractSize sz) =
    (Type 129, empty,
     s2par ("Extracting or updating a bit vector of size " ++ show sz ++ " is not supported."))

getErrorText (EBadExtractIndex idx) =
    (Type 130, empty,
     s2par ("Extracting or updating a bit vector using " ++ show idx ++ " as an index is not supported."))

getErrorText (ENotNumEq t1 t2 poss) =
   (Type 131, empty,
    let msg = s2par ("The numeric types " ++ ishow t1 ++ " and " ++ ishow t2 ++
                     " could not be shown to be equal.")
        unique_poss = nub poss
        pos_str = if (length unique_poss == 1) then "position" else "positions"
        msg_extra = s2par ("This equality was required at the following " ++
                           pos_str ++ ":") $$
                    nest 2 (vcat (map (text . prPosition) unique_poss))
    in  if null poss
        then msg
        else msg $$ msg_extra
   )

getErrorText (EInvalidSizedLiteral lit sz) =
    (Type 132, empty,
     s2par ("The value " ++ lit ++ " does not fit in " ++ itos sz ++ " bits."))

getErrorText (ECtxErrPrimParam ty poss hasVar) =
    (Type 133, empty,
     let s = if (length poss > 1) then "s" else ""
         intro_msg =
           s2par ("Parameters to imported modules can be of type " ++
                  "Integer, String, Real, or any type which has an " ++
                  "instance of Bits. A parameter of type " ++ quote ty ++
                  " is declared at the following position" ++ s ++ ":") $$
           nest 2 (vcat (map (text . prPosition) (nub poss)))
         proviso_msg ps =
           s2par ("Perhaps a proviso is needed:") $$
           -- should only be one Bits proviso, but just in case...
           nest 2 (vcat (map text ps))
     in  case hasVar of
           Nothing -> intro_msg
           Just ps -> intro_msg $$ proviso_msg ps
    )
getErrorText (ECtxErrPrimPort ty poss hasVar) =
    (Type 134, empty,
     let s = if (length poss > 1) then "s" else ""
         intro_msg =
           s2par ("Ports of imported modules can be of any type which " ++
                  "has an instance of Bits. " ++
                  "A port of type " ++ quote ty ++
                  " is declared at the following position" ++ s ++ ":") $$
           nest 2 (vcat (map (text . prPosition) (nub poss)))
         proviso_msg ps =
           s2par ("Perhaps a proviso is needed:") $$
           -- should only be one Bits proviso, but just in case...
           nest 2 (vcat (map text ps))
     in  case hasVar of
           Nothing -> intro_msg
           Just ps -> intro_msg $$ proviso_msg ps
    )

getErrorText (EClassFundepsOverlap cls) =
    (Type 135, empty,
     s2par ("A dependency for typeclass " ++ quote cls ++
            " mentions the same variable as both as source and a target."))
getErrorText (EClassFundepsExtra cls extra_vs) =
    (Type 136, empty,
     s2par ("Dependencies for typeclass " ++ quote cls ++
            " mention the following variables which are not parameters " ++
            "of the typeclass: " ++ intercalate ", " extra_vs))
getErrorText (EClassFundepsEmpty cls) =
    (Type 137, empty,
     s2par ("Dependencies for typeclass " ++ quote cls ++
            " include an empty list.  Valid dependencies must have " ++
            "at least one source variable and at least one target variable."))

getErrorText (ENotStruct t f) =
    (Type 138, empty,
     s2par ("The expression does not have a field " ++ quote f ++
            " because it is not a struct or interface.  Found type: ") $$
     nest 2 (text t))
getErrorText (EFieldsNotVis t) =
    (Type 139, empty,
     s2par ("Cannot access fields in this expression since its type " ++
            quote t ++ " is abstract.  The type was imported from a " ++
            "package that did not export its representation, so any " ++
            "fields that it may have are not visible."))
getErrorText (EFieldsNotImp t p) =
    (Type 140, empty,
     let ex_str = if (p == "")
                  then "." -- this shouldn't happen
                  else ", e.g., `import " ++ p ++ "::*;'"
     in s2par ("Cannot access fields in this expression since its type " ++
               quote t ++ " has not been imported.  Perhaps an import " ++
               "statement is missing" ++ ex_str))
getErrorText (ENoTopTypeSign n) =
  (Type 141, empty, s2par $ "Top-level definition of " ++ ishow n ++ " has no type signature.")
getErrorText (EConPatArgs c mt expected actual) =
  (Type 142, empty, s2par ("Pattern for constructor " ++ ishow c ++ (maybe " " (" of type " ++) mt) ++
                           " requires " ++ show expected ++ " arguments," ++ " found " ++ show actual ++ "."))

-- XXX Errors about constructor argument mismatches should contain the type of
-- the constructor, but this is overly hard to actually compute.
getErrorText (EConMismatchNumArgs e {-t-} n1 n2) =
    (Type 143, empty,
     s2par "Too many arguments in the use of the following constructor:" $$
     nest 2 (text e) $$
     s2par ("The constructor expects " ++ show n1 ++
            " arguments but was used with " ++ show n2 ++ " arguments.") {-
     $$
     if n1 > 0
     then
       s2par "Constructor has type:" $$
       nest 2 (text t)
     else text "" -}
     )

getErrorText (EPartialConMismatchNumArgs e t1 {-t2-} n1 n2 n3) =
    (Type 144, empty,
     s2par "Wrong number of arguments in the partial application of the following constructor:" $$
     nest 2 (text e) $$
     s2par ("The constructor expects " ++ show n1 ++
            " arguments and was used with " ++ show n2 ++
            " arguments, leaving " ++ show (n1 - n2) ++
            " unfilled, however a function " ++
            if n3 > 0
            then  "with " ++ show n3 ++ " arguments was expected."
            else "was not expected.") $$
     s2par "The expected type is:" $$
     nest 2 (text t1){-
     $$ if n1 > 0
     then
       s2par "Constructor has type:" $$
       nest 2 (text t2)
     else text ""-})

getErrorText (EStringOf s) =
  (Type 145, empty, s2par ("Cannot take stringOf " ++ ishow s ++ " (symbol might not be in scope)"))
getErrorText (EKindStrForNum i) =
  (Type 146, empty, s2par ("The string type " ++ ishow i ++ " was found where a numeric type was expected."))
getErrorText (EKindStrForStar i) =
  (Type 147, empty, s2par ("The string type " ++ ishow i ++ " was found where a value type was expected."))
getErrorText (EKindStarForStr i) =
  (Type 148, empty, s2par ("The value type " ++ ishow i ++ " was found where a string type was expected."))
getErrorText (EKindNumForStr i) =
  (Type 149, empty, s2par ("The numeric type " ++ ishow i ++ " was found where a string type was expected."))
getErrorText (EStrKindArg) =
  (Type 150, empty, s2par "String types do not take arguments.")

getErrorText (EConstrFieldsNotNamed c t) =
    (Type 151, empty,
     s2par ("Constructor " ++ quote c ++ " for type " ++ quote t ++
            " does not have named fields."))

-- Generation Errors

getErrorText (EGenerate num s) =
    (Generate num, empty, s2par s)
getErrorText (EHasWhen s) =
    (Generate 0, empty, s2par ("Verilog modules may not have arguments using " ++ quote "when" ++ "."))

getErrorText (EFewPorts state port has needs) =
    (Generate 1, empty, s2par ("The state element " ++ state ++ " on port " ++ port ++ " has " ++ show has ++
                        " connections, needs " ++ show needs ++ " connections (deprecated)."))
getErrorText (EResources meth ports calls) =
    (Generate 2, empty, s2par (ishow meth ++ " needs more than " ++ show ports ++ " ports for the following uses:") $$
                        nest 4 (vcat (map show_call calls)))
  where
      show_call (expr, pos) = s2par (ishow expr ++ " at " ++ pos)
getErrorText (EArbitrate mod rs) =
    (Generate 3, empty, if (length rs > 1) then
                           s2par ("Arbitrating in module " ++ ishow mod
                           ++ (if length rs > 2 then " among" else " between")
                           ++ " rules " ++ (unwordsAnd (map ishow rs)) ++ ".")
                        else
                           internalError "EArbitrate needs 2+ args")

getErrorText (EParActionRangeConflict r u1 u2) =
    (Generate 4, empty,
     let intro = s2par ("Rule " ++ quote r ++
                        " uses methods that conflict in parallel:")
         moreInfo = if (fth4 u1 || fth4 u2)
                    then s2par ("For the complete expressions use the flag " ++
                                quote "-show-range-conflict" ++ ".")
                    else empty
         ppUse (meth, hasCond, args, _) =
             let mcall =  text meth <> text "(" <> args <> text ")"
             in  nest 2 $ case (hasCond) of
                              Nothing -> mcall
                              Just c -> text "if (" <> c <> text ")" $$
                                        nest 2 mcall
     in  intro $$ ppUse u1 $$ text "and" $$ ppUse u2 $$ moreInfo)

getErrorText (ERuleAssertion ruleId assertion mreason) =
    (Generate 5, empty,
     let intro = s2par ("The assertion " ++ ishow assertion ++
                        " failed for rule " ++ ishow ruleId)
     in  case mreason of
           Nothing -> intro
           Just reason -> intro $$ reason
    )

getErrorText (ENotAlwaysReady i) =
    (Generate 6, empty, s2par ("Method(s) not always ready: " ++ i))

getErrorText (EClockDomain object name clock_domains) =
    (Generate 7, empty,
     s2par ("Reference across clock domain in " ++ object ++ " " ++
            quote name ++ ".") $$
     prMethodsByClockDomain clock_domains)

-- Removed Generate 8, WInterfaceArg since synthesis of interface module
-- args changed from an experimental feature (which produced a warning) to
-- an outright unsupported feature (producing an error).

getErrorText (EInterfaceArg f) =
    (Generate 8, empty, s2par ("Separate code generation for module " ++ ishow f ++
                               ", which has an interface argument, is not supported"))

getErrorText (WCycleDrop child root cycle) =
    (Generate 9, empty, s2par "The scheduling phase created a conflict between the following rules:" $$
                        nest 4 (s2par (ishow child ++ " and " ++ ishow root)) $$
                        s2par "to break the following cycle:" $$
                        nest 4 (s2par (intercalate " -> " (map ishow cycle))))
getErrorText (WUrgencyChoice { em_more_urgent = moreUrgent,
                               em_less_urgent = lessUrgent,
                               em_conflicts = conflicts_info }) =
   let ending | isEmpty conflicts_info = char '.'
              | otherwise = char '.' <+> text "Conflicts:"
   in (Generate 10, empty,
       fsep ([text "Rule", doubleQuotes moreUrgent] ++
             s2docs "was treated as more urgent than" ++
             [doubleQuotes lessUrgent <> ending]) $+$
       nest 2 conflicts_info)

getErrorText (EModuleUndet) =
    (Generate 11, empty, s2par "Trying to generate a module from a don't-care value")
getErrorText (EStringNF s) =
    (Generate 12, empty, s2par ("Not a compile time string: " ++ s))
getErrorText (ENoNF t s) =
    (Generate 13, empty, s2par "Compile time expression did not evaluate:" $$ s2par ("Type: " ++ t) $$ text s)
getErrorText (EHasImplicit s) =
    (Generate 14, empty, s2par ("Implicit condition not allowed for expression: " ++ s))

getErrorText (EEnableNotHigh inst ports) =
    (Generate 15, empty,
     s2par ("Instance " ++ quote inst ++ " requires the following method" ++
            plural_s ++ " to be always enabled, but the condition" ++ plural_s ++
            " for executing the method" ++ plural_s ++ " could not be proven " ++
            "to be always True:") $+$
     nest 2 (sepList (map text ports) comma) $+$
     s2par ("The behavior of the design will likely be incorrect if the " ++
            "method" ++ plural_s ++ " " ++ be_verb ++ " not enabled on every " ++
            "clock cycle."))
    where (plural_s, be_verb) =
              case ports of
                [_] -> ("", "is")
                _   -> ("s", "are")

getErrorText (ESplitInsideNoSplit expr) =
    (Generate 16, empty, s2par "Splitting if-expression inside non-splitting if-expression:" $$ text expr)

getErrorText (WMissingRule s) =
    (Generate 17, empty, s2par ("Rule not found: " ++ ishow s))

-- Generate 19 is obsolete.  It used to be that Generate 18 was for
-- reporting WFCall of one method with one position and Generate 19 was
-- for one method with multiple positions.
-- They were combined into one, which also allows displaying with no position
-- (in case all the positions are bad)

-- Generate 18 is also obsolete.  G0020 used to be just an intro message to
-- explain the G0018 and G0019 message that followed.  Now, all methods
-- for a module are reported in one G0020 warning.

-- before calling this, remember to nub and remove bad positions
-- (position in the Prelude, position in bi file, etc)
getErrorText (WFCall method_infos) =
    (Generate 20 , empty,
     let hdr = s2par ("System functions (e.g., $display) called by " ++
                      "interface methods execute in an unpredictable " ++
                      "order during Verilog simulations.")
         -- XXX note that the method's position is ignored
         -- XXX do we even need to report the positions inside the methods?
         show_meth (method, pos, positions) =
             let m_str = "Top-level interface method " ++ ishow method ++
                         " calls a system function (e.g., $display)"
             in  case (positions) of
                   []    -> s2par m_str
                   [pos] -> s2par (m_str ++ " at " ++ prPosition pos)
                   poss  -> s2par (m_str ++ " at the following positions:") $$
                            nest 4 (vcat (map (text . prPosition) poss))
     in
         hdr $$
         nest 4 (vcat (map show_meth method_infos))
    )

getErrorText (WRuleNeverFires rule drop) =
    (Generate 21, empty,
     s2par ("According to the generated schedule, rule " ++ quote rule ++
            " can never fire." ++ (if drop then dropping else [])))

getErrorText (WMethodNeverReady method) =
    (Generate 22, empty,
     s2par ("According to the generated schedule, method " ++ quote method ++
            " is never ready."))

getErrorText (WRuleAlwaysFalse rule drop) =
    (Generate 23, empty,
     s2par ("The condition for rule " ++ quote rule ++ " is always false."
            ++ (if drop then dropping else [])))

getErrorText (WRuleNoActions rule drop) =
    -- XXX G0023 is already used by WRuleAlwaysFalse
    (Generate 23, empty,
     s2par ("The body of rule " ++ quote rule ++ " has no actions."
            ++ (if drop then dropping else [])))

getErrorText (WTooManySteps i c w m) =
    (Generate 24, empty, s2par ("The function unfolding steps interval has been exceeded when unfolding " ++ ishow i ++ ".\n" ++
                                "The current number of steps is " ++ (show c) ++ ". Next warning at " ++ (show w) ++  " steps.\n" ++
                                if (m /= 0) then "Elaboration terminates at " ++ (show m) ++ " steps." else ""))

getErrorText (ETooManySteps i m) =
    (Generate 24, empty, s2par ("The maximum number of function unfolding steps has been exceeded when unfolding " ++ ishow i ++ ".\n" ++
                     "You can use the flags \"-steps N\", \"-steps-warn-interval N\", and \"-steps-max-intervals N\" to set the maximum number of steps.\n" ++
                     "The current maximum is " ++ m ++ "."))

getErrorText (EStepsIntervalError i c n) =
    (Generate 24, empty, s2par ("The function unfolding steps interval has been exceeded when unfolding " ++ ishow i ++ ".\n" ++
                                "Evaluation has been terminated because a separate error has been detected.\n" ++
                                "The current number of steps is " ++ (show c) ++ ".\n" ++
                                "You can use the flag \"-steps-warn-interval N\" to set the number of steps in an interval.\n" ++
                                "The current number of steps in an interval is " ++ (show n) ++ "."))

getErrorText (EModuleUndetNoMatch) =
    (Generate 25, empty, s2par "Trying to generate a module which is undefined because of an incomplete pattern match.")

getErrorText (ECombCycle names) =
    (Generate 26, empty, s2par "Combinational cycle detected through the following signals: " $$
                                brackets (sepList (map text names) comma))

getErrorText (ENetInstConflict s) =
    (Generate 27, empty, s2par("The generated net id \"" ++ s  ++ "\" conflicts with an instance of the same name."))
getErrorText (EUninitialized name) =
    (Generate 28, empty, s2par (quote name ++ " uses uninitialized value " ++
                       "(the position shown is the object's declaration).\n" ++
                       "If this error is unexpected, please consult KPNS #32."))
getErrorText (EUnknownRuleId name) =
    (Generate 29, empty, s2par ("Unknown rule " ++ quote name))
getErrorText (EUrgencyCycle cycle explanations other_ids) =
    (Generate 30, empty,
     let intro = s2par ("A cycle was detected in the urgency requirements " ++
                        "for this module:") $$
                 nest 2 (s2par (intercalate " -> " (map ishow cycle)))
         expl = s2par ("The relationships were introduced for " ++
                       "the following reasons:") $$
                nest 2 (vcat explanations)
         others = s2par ("This cycle also extends through the following " ++
                         "other rules/methods:") $$
                  nest 2 (sepList (map text other_ids) comma)
     in  if null other_ids
         then intro $$ expl
         else intro $$ expl $$ others
    )

-- Removed Generate 31, EMethodUrgency, since attrs are supported on methods

getErrorText (EPreSchedCycle cycle_doc) =
    (Generate 32, empty,
     s2par ("A cycle was detected in the design prior to scheduling.  " ++
            "It is likely that an action in this module uses " ++
            "circular logic.  The cycle is through the following:") $$
     nest 2 cycle_doc)

getErrorText (ESelfUrgency ruleId path_doc) =
    (Generate 33, empty,
     s2par ("The condition of rule " ++ quote ruleId ++ " " ++
            "depends on the firing of that rule.  This is due to the " ++
            "following path from the rule's WILL_FIRE to its CAN_FIRE:") $$
     nest 2 path_doc)

getErrorText (EPathMethodArgToRdy methodId argId path_doc) =
    (Generate 34, empty,
     s2par ("The ready condition for method " ++ quote methodId ++ " " ++
            "depends on the argument " ++ quote argId ++ " " ++
            "of that method.  This is due to the following path:") $$
     nest 2 path_doc)

getErrorText (EPathMethodEnToRdy methodId path_doc) =
    (Generate 35, empty,
     s2par ("The ready condition for method " ++ quote methodId ++ " " ++
            "depends on the enable signal of that method.  " ++
            "This is due to the following path:") $$
     nest 2 path_doc)

getErrorText (WEarlinessChoice { em_more_early = more_early,
                                 em_less_early = less_early,
                                 em_conflicts = conflicts_info }) =
   let ending | isEmpty conflicts_info = char '.'
              | otherwise = char ',' <+> text "affecting:"
   in  (Generate 36, empty,
        fsep ([text "Rule", doubleQuotes more_early] ++
              s2docs "will appear to fire before" ++
              [doubleQuotes less_early] ++
              s2docs ("when both fire in the same clock") ++
              [text "cycle" <> ending]) $+$
              nest 2 conflicts_info)

getErrorText (EClockArgSiblings mod_name inst_name clock_pairs) =
    (Generate 37, empty,
     let prClkPair (clk1, clk2) = "(" ++ clk1 ++ ", " ++ clk2 ++ ")"
     in  s2par ("Clock arguments to module " ++ quote mod_name ++
                " which are expected to be in the same family " ++
                "have been connected to clocks from different domains" ++
                (if (inst_name /= "")
                 then ", in the instantiation of " ++ quote inst_name
                 else "") ++ ".") $$
         s2par ("The following clock pairs should be in the same domain:") $$
         nest 2 (vcat (map (s2par . prClkPair) clock_pairs)))

getErrorText (WClockOfClocks clock_domains) =
    (Generate 38, empty,
     s2par ("Multiple contributing clocks were found in the argument to " ++
            quote "clockOf" ++ ". Use " ++ quote "clocksOf" ++
            " to extract all of the clocks or change the argument expression.") $$
     prMethodsByClockDomain clock_domains)

getErrorText (WMethodAnnotChange method1 method2 path) =
    (Generate 39, empty,
     s2par ("The scheduling relationship between method " ++ ishow method1 ++
            " and method " ++ ishow method2 ++ " was changed to SBR " ++
            "because the following rules can only execute between them:") $$
     nest 2 (sepList (map text path) comma))

getErrorText (EReflexiveUserUrgency ruleId pos1 pos2) =
    (Generate 40, empty,
     s2par ("A rule cannot be more urgent than itself.") $$
     s2par ("The rule " ++ ishow ruleId ++ " appears twice in the same " ++
            "attribute at the following positions:") $$
     nest 2 (text (prPosition pos1)) $$
     nest 2 (text (prPosition pos2)))

getErrorText (ECombinedSchedCycle cycle explanations other_ids) =
    (Generate 41, empty,
     let intro = s2par ("A cycle was detected in the ordering requirements " ++
                        "for this module:") $$
                 nest 2 (s2par (intercalate " -> " (map ishow cycle)))
         expl = s2par ("The relationships were introduced for " ++
                       "the following reasons:") $$
                nest 2 (vcat explanations)
         others = s2par ("This cycle also extends through the following " ++
                         "other rules/methods:") $$
                  nest 2 (sepList (map text other_ids) comma)
         to_do = s2par ("To resolve this cycle, consider removing an " ++
                        "urgency dependency from the cycle or removing " ++
                        "an execution order requirement (by causing the " ++
                        "two rules to conflict or be mutually exclusive).")
     in  if null other_ids
         then intro $$ expl $$ to_do
         else intro $$ expl $$ others $$ to_do
    )

getErrorText (EResetClocks mod_name inst_name resets) =
    (Generate 42, empty,
     let prReset (rst_name, port_name) =
             rst_name ++ if (port_name /= "")
                           then " (" ++ port_name ++ ")"
                           else ""
     in
       s2par ("Reset arguments are used in the wrong clock domains " ++
              "in the inputs to module " ++ quote mod_name ++
              (if (inst_name /= "")
               then " in the instantiation of " ++ quote inst_name
               else "") ++ ".  " ++
              "Resets cannot be used across clock domains without " ++
              "passing through a reset synchronizer.") $$
       s2par ("Resets were connected incorrectly to the following inputs:") $$
       nest 2 (vcat (map (s2par . prReset) resets)))

getErrorText (WMultipleResets object name reset_list) =
    (Generate 43, empty,
     s2par ("Multiple reset signals influence " ++ object ++ " " ++
            quote name ++ ".") $$
     s2par ("This can lead to inconsistent, non-atomic results when not all of these signals are asserted.") $$
     prMethodsByReset reset_list)

getErrorText (WResetOfResets reset_list) =
    (Generate 44, empty,
     s2par ("Multiple contributing reset signals were found in the argument to " ++
            quote "resetOf" ++ ". Use " ++ quote "resetsOf" ++
            " to extract all of the resets or change the argument expression.") $$
     prMethodsByReset reset_list)

getErrorText (EMethodNoBoundaryClock name) =
    (Generate 45, empty,
     s2par ("Method " ++ quote name ++ " is unusable because " ++
            "it is connected to a clock not available at the module boundary."))

getErrorText (WMethodNoBoundaryReset name) =
    (Generate 46, empty,
     s2par ("Reset information for method " ++ quote name ++ " is lost " ++
            "because the reset is not available at the module boundary."))
getErrorText (EUndeterminedClock) =
    (Generate 47, empty, s2par "Attempt to use this undetermined clock")
getErrorText (EUndeterminedReset) =
    (Generate 48, empty, s2par "Attempt to use this undetermined reset")
getErrorText (EUndeterminedInout) =
    (Generate 49, empty, s2par "Attempt to use this undetermined inout")
getErrorText (EUnexpectedOutputClkGate name) =
    (Generate 50, empty,
     s2par ("Output clock " ++ quote name ++ " was expected to be ungated, but has a nontrivial gate condition."))

getErrorText (WOutputResetNoBoundaryClock reset) =
    (Generate 51, empty,
     s2par ("Output reset " ++ quote reset ++
            " is associated with a clock domain " ++
            "but no input or output clock on the module boundary is " ++
            "in that domain, so the reset is being marked as clocked by " ++
            quote "no_clock" ++ "."))

-- Removed Generate 51, WMethodAnnotChangeArb. This is not needed since we
-- no longer consult the flattened execution order to determine if a rule
-- executes between two methods.

-- Removed Generate 52, WSchedulerEffortLimit, only needed for CUDD SAT solver

getErrorText (EModParameterDynamic inst_name param_name) =
    (Generate 53, empty,
     s2par ("Parameter " ++ quote param_name ++
            " of submodule " ++ quote inst_name ++
            " is instantiated with a dynamic expression.  " ++
            "Instantiation parameters must have static values."))

getErrorText (EUnknownRuleIdAttribute name ) =
    (Generate 54, empty, s2par ("Rule " ++ quote name ++ " was referenced in a rule attribute before it was defined."))

getErrorText (EPortNamesClashFromMethod m1 m2 port loc ) =
    (Generate 55, empty,
     s2par ("Method " ++ quote m1 ++ " generates a port with name " ++ quote port ++
            " which conflicts with a port of the same name generated by method " ++ quote m2 ++
            " at location " ++ prPosition loc ++ "."))

-- Removed Generate 56 EUnsupportedRuleUrgency
-- Removed Generate 57 EUrgentRuleConflict
-- Both removed because rules can now be more urgent than methods.

getErrorText (EBSimDynamicArg inst_name param_names) =
    (Generate 58, empty,
     s2par ("Dynamic module arguments are not supported by Bluesim.  " ++
            "Submodule " ++ quote inst_name ++
            " is instantiated with a dynamic expression for the " ++
            " following arguments:") <+>
     quoteStrList param_names <> text ".")

getErrorText (EDivideByZero) =
    (Generate 59, empty,
     s2par ("Division by zero occurred during elaboration."))

getErrorText (EIntegerNegativeExponent) =
    (Generate 60, empty,
     s2par ("Integer exponentiation to a negative power occurred " ++
            "during elaboration"))

getErrorText (EMERulesIdentical rule_0 rule_1) =
    (Generate 61, empty,
     s2par("The rules " ++ quote rule_0 ++ " and " ++ quote rule_1  ++ " have been annotated as mutually exclusive, but they cannot be mutually exclusive since their rule conditions (including both explicit and implicit conditions) are identical."))

getErrorText (EBSimEnablePragma) =
    (Generate 62, empty,
     s2par ("Bluesim does not currently support designs with always-enabled or enabled-when-ready attributes on the the top-level interface.  Consider wrapping the design in a testbench with an empty interface."))

getErrorText (EClkGateNotInhigh mod inst clk) =
    (Generate 63, empty,
     s2par ("The module " ++ quote mod ++ " expects the input clock " ++
            quote clk ++ " to be ungated, but in the instantiation " ++
            quote inst ++ " it has been connected to a clock whose gate " ++
            "is not constant True."))

getErrorText (EAttributeIdNotAMethod name) =
    (Generate 64, empty,
     s2par ("The attribute value " ++ quote name ++
            " is not a method of this module."))

getErrorText (EAttributeIdNotAnInputClock name) =
    (Generate 65, empty,
     s2par ("The attribute value " ++ quote name ++
            " is not an input clock of this module."))

getErrorText (EEnableAlwaysLow inst ports) =
    (Generate 66, empty,
     s2par ("Instance " ++ quote inst ++ " requires the following method" ++
            plural_s ++ " to be always enabled, but the condition" ++ plural_s ++
            " for executing the method" ++ plural_s ++ " " ++ be_verb ++
            " always False:") $+$
     nest 2 (sepList (map text ports) comma) $+$
     s2par ("This can be because the method" ++ plural_s ++ " " ++ be_verb ++
            " not used in any rules or because the condition of those uses " ++
            "can be shown to be False."))
    where (plural_s, be_verb) =
              case ports of
                [_] -> ("", "is")
                _   -> ("s", "are")

getErrorText (EDynamicClock) =
    (Generate 67, empty,
     s2par ("The expression for a clock could not be evaluated. " ++
            "Clocks must be determined at compile time and cannot be " ++
            "computed dynamically."))
getErrorText (EDynamicReset) =
    (Generate 68, empty,
     s2par ("The expression for a reset could not be evaluated. " ++
            "Resets must be determined at compile time and cannot be " ++
            "computed dynamically."))
getErrorText (EDynamicRules) =
    (Generate 69, empty,
     s2par ("The expression for a rule or rules could not be evaluated. " ++
            "Rules must be determined at compile time and cannot be " ++
            "computed dynamically."))
getErrorText (EDynamicModule) =
    (Generate 70, empty,
     s2par ("The expression for a module instantiation could not be evaluated. " ++
            "Modules must be determined at compile time and cannot be " ++
            "computed dynamically."))

getErrorText (EDynamicInputClock inst_name clock_name) =
    (Generate 71, empty,
     s2par ("Input clock " ++ quote clock_name ++
            " of submodule " ++ quote inst_name ++
            " is instantiated with a dynamic expression.  " ++
            "Input clocks must be determined at compile time."))
getErrorText (EDynamicInputReset inst_name reset_name) =
    (Generate 72, empty,
     s2par ("Input reset " ++ quote reset_name ++
            " of submodule " ++ quote inst_name ++
            " is instantiated with a dynamic expression.  " ++
            "Input resets must be determined at compile time."))
getErrorText (ECrossDomainMethodUse meth calls) =
    (Generate 73, empty, s2par ("Method " ++ (ishow meth) ++ " is used in multiple clock domains:") $$
                        nest 4 (vcat (map show_call calls)))
  where
      show_call (expr, pos) = s2par (ishow expr ++ " at " ++ pos)
getErrorText (ECrossDomainPragma pragmas) =
    (Generate 74, empty, s2par "An annotation cannot involve rules in multiple clock domains:" $$
                        nest 4 (vcat (map text pragmas)))

getErrorText (EInResetToMultipleDomainArgs rst_name mod_name inst_name resets) =
    (Generate 75, empty,
     let prReset (rst_name, port_name) =
             rst_name ++ if (port_name /= "")
                           then " (" ++ port_name ++ ")"
                           else ""
     in
       s2par ("The input reset " ++ quote rst_name ++
              " is used in multiple clock domains in the inputs to module " ++
              quote mod_name ++
              (if (inst_name /= "")
               then " in the instantiation of " ++ quote inst_name
               else "") ++ ".  " ++
              "Resets cannot be used across clock domains without " ++
              "passing through a reset synchronizer.") $$
       s2par ("This reset was connected to the following inputs:") $$
       nest 2 (vcat (map (s2par . prReset) resets)))

getErrorText (WInputResetNoBoundaryClock reset) =
    (Generate 76, empty,
     s2par ("Input reset " ++ quote reset ++
            " is associated with a clock domain " ++
            "but no input or output clock on the module boundary is " ++
            "in that domain, so the reset is being marked as clocked by " ++
            quote "no_clock" ++ "."))

getErrorText (EClkGateNotUnused clk) =
    (Generate 77, empty,
     s2par ("The gate of the clock " ++ quote clk ++ " is used within the " ++
            "module, but is marked with an attribute as being unused."))

-- Reserved Generate 78 EUpdateUndeterminedListOrArray
-- Reserved Generate 79 EUpdateListOrArrayUndeterminedIndex
-- Reserved Generate 80 EUndeterminedListOrArrayLength
-- These 3 errors are now reserved and generated by library code in the
-- prelude instead of in the compiler itself.

getErrorText (EModPortHasImplicit inst_id arg_id) =
    (Generate 81, empty,
     s2par ("Module arguments cannot have implicit conditions. " ++
            "The expression for argument " ++ quote arg_id ++
            " in the instantiation of " ++ quote inst_id ++
            " has an implicit condition."))

getErrorText (EPortExprClockDomain port port_clkinfo expr_clks) =
    (Generate 82, empty,
     let intro = s2par ("The value assigned to module argument " ++
                        quote port ++ " is in the wrong clock domain.")
         port_msg =
           case (port_clkinfo) of
             Nothing ->
                 s2par ("The port was declared with no clock, " ++
                        "but the expression for the value has a clock.")
             Just (port_clknames, port_clks) ->
                 s2par ("Input/output clocks of the module " ++
                        "which are in the domain of the port:") $$
                 nest 2 (sepList (map text port_clknames) comma) $$
                 s2par ("Clocks connected to those inputs/outputs:") $$
                 nest 2 (sepList (map text port_clks) comma)
         arg_msg =
             s2par ("Clocks of the expression:") $$
             nest 2 (sepList (map text expr_clks) comma)
     in
         intro $$ port_msg $$ arg_msg
    )

getErrorText (WPortExprReset port port_rst method_calls) =
    (Generate 83, empty,
     s2par ("The value assigned to module argument " ++ quote port ++
            " is influenced by a different reset signal than expected " ++
            "by the module.") $$
     s2par ("This can lead to inconsistent, non-atomic results when not " ++
            "all of these signals are asserted.") $$
     s2par ("The input reset expected by the module:") $$
     nest 2 (text port_rst) $$
     s2par ("Method calls in the expression:") $$
     nest 2 (sep (map pMeth method_calls)))
  where pMeth (s, pos) =
            text s <+>
            if (isUsefulPosition pos)
              then text ("at") <+> text (prPosition pos) <> comma
              else empty

getErrorText (EBSimForeignImport mod_name inst_name parent_mod_name) =
    (Generate 84, empty,
     s2par ("Bluesim does not currently support imported Verilog modules.  " ++
            "The instantiation " ++ ishow inst_name ++
            " in parent module " ++ ishow parent_mod_name ++
            " is an imported Verilog module " ++ ishow mod_name ++ "."))

getErrorText (EInvalidLog) =
    (Generate 85, empty,
     s2par ("A logarithm operator was applied to a non-positive number " ++
            "during elaboration."))

getErrorText (EClockArgAncestors mod_name inst_name clock_pairs) =
    (Generate 86, empty,
     let prClkPair (clk1, clk2) = "(" ++ clk1 ++ ", " ++ clk2 ++ ")"
     in  s2par ("Clock arguments to module " ++ quote mod_name ++
                " which are expected to have an ancestry relationship" ++
                " have been connected to clocks which are not ancestors" ++
                (if (inst_name /= "")
                 then ", in the instantiation of " ++ quote inst_name
                 else "") ++ ".") $$
         s2par ("The following clock pairs should have an (ancestor,child)" ++
                " relationship:") $$
         nest 2 (vcat (map (s2par . prClkPair) clock_pairs)))

getErrorText (EPoisonedDef name) =
    (Generate 87, empty, fsep msg)
  where msg = s2docs "Code generation failed because the definition" ++ [qname] ++
              s2docs "whose compilation failed with errors, was used during elaboration." ++
              s2docs "You should correct the errors with the definition of" ++ [qname] ++
              s2docs "or stop using it in your design before proceeding."
        qname = text "'" <> name <> text "'"

getErrorText (WPoisonedDefFile file) =
    (Generate 88, empty, fsep (s2docs msg))
  where msg = "File " ++ file ++ " contains definitions that did not compile successfully."

getErrorText (EDynamicArgInout inst_name inout_name) =
    (Generate 89, empty,
     s2par ("Inout " ++ quote inout_name ++
            " of submodule " ++ quote inst_name ++
            " is instantiated with a dynamic expression.  " ++
            "Inouts must be determined at compile time."))

getErrorText (WIfcInoutNoBoundaryClock inout) =
    (Generate 90, empty,
     s2par ("Inout subinterface " ++ quote inout ++
            " is associated with a clock " ++
            "which is not available on the module boundary, " ++
            "so the inout is being marked as clocked by " ++
            quote "no_clock" ++ "."))
getErrorText (WIfcInoutNoBoundaryReset inout) =
    (Generate 91, empty,
     s2par ("Inout subinterface " ++ quote inout ++
            " is associated with a reset " ++
            "which is not available on the module boundary, " ++
            "so the inout is being marked as reset by " ++
            quote "no_reset" ++ "."))

-- Removed: Generate 92
-- Removed: Generate 93

getErrorText (EDynamicInout) =
    (Generate 94, empty,
     s2par ("The expression for a inout could not be evaluated. " ++
            "Inouts must be determined at compile time and cannot be " ++
            "computed dynamically."))

getErrorText (EMethodSchedToExec method cycle explanations) =
    (Generate 95, empty,
     let intro = s2par ("A path containing rules was detected between the scheduling of " ++
                        "method " ++ quote method ++ " and its execution.  " ++
                        "This is not allowed, as the method may be called " ++
                        "conditionally inside a rule in the parent " ++
                        "module.  The path is as follows:") $$
                 nest 2 (s2par (intercalate " -> " (map ishow cycle)))
         expl = s2par ("The relationships were introduced for " ++
                       "the following reasons:") $$
                nest 2 (vcat explanations)
         to_do = s2par ("To resolve this, consider removing an " ++
                        "urgency dependency from the path or removing " ++
                        "an execution order requirement (for example, " ++
                        "by causing the two rules to conflict or be " ++
                        "mutually exclusive).  Removing the synthesis " ++
                        "boundary for this module may also help.")
     in  intro $$ expl $$ to_do
    )

getErrorText (EDynamicExecOrderOneRule rule uses) =
    (Generate 96, empty,
     let intro =
           s2par("The rule " ++ quote rule ++ " requires dynamic " ++
                 "scheduling, which is not supported by Bluesim.  " ++
                 "This is because the rule uses methods which have a " ++
                 "rule that executes between them in the static execution " ++
                 "order of the separately synthesized submodule.  " ++
                 "See entry #29 in the KPNS document for more information " ++
                 "and possible solutions.")
         showMeth (m1,m2,rs) =
             s2par ("(" ++ m1 ++ ", " ++ m2 ++ ")") $$
             nest 2 (sepList (map text rs) comma)
         debug =
           s2par ("The methods and the rules between them are as follows:") $$
           nest 2 (vcat (map showMeth uses))
    in
        intro $$ debug
   )

getErrorText (EBSimInoutIfc ifc_names) =
    (Generate 97, empty,
     s2par ("Inout interfaces are not supported by Bluesim.  " ++
            "This module has the following Inout subinterfaces:") <+>
     quoteStrList ifc_names <> text ".")
getErrorText (EBSimInoutArg maybe_submod arg_names) =
    (Generate 98, empty,
     let loc = case (maybe_submod) of
                 Nothing -> "This module"
                 Just submod -> "Submodule " ++ quote submod
     in  s2par ("Inout module arguments are not supported by Bluesim.  " ++
                loc ++ " has the following Inout arguments:") <+>
         quoteStrList arg_names <> text ".")

getErrorText (EBSimTopLevelArgOrParam is_sysc names) =
    let hdr = if is_sysc
              then "Top-level module parameters and arguments are not " ++
                   "supported by BSV-to-SystemC.  The following parameters " ++
                   "and arguments to the top-level module are not supported:"
              else "Top-level module parameters and arguments are not " ++
                   "supported by Bluesim.  The following parameters and " ++
                   "arguments to the top-level module are not supported:"
    in (Generate 99, empty,
        (s2par hdr) $+$ (nest 2 (quoteStrList names <> text ".")))

getErrorText (EDynamicExecOrderTwoRules rule1 rule2 uses path explanations) =
    (Generate 100, empty,
     let intro =
           s2par("The rules " ++ quote rule1 ++ " and " ++ quote rule2 ++
                 " require dynamic scheduling, which is not supported by " ++
                 "Bluesim.  This is because the rules use methods which " ++
                 "have a rule that executes between them in the static " ++
                 "execution order of the separately synthesized submodule, " ++
                 "but the rules must execute in the opposite order " ++
                 "according to the current module's schedule.  " ++
                 "See entry #30 in the KPNS document for more information " ++
                 "and possible solutions.")
         showMeth (m1,m2,rs) =
             s2par ("(" ++ m1 ++ ", " ++ m2 ++ ")") $$
             nest 2 (sepList (map text rs) comma)
         debugMeth =
           s2par ("The methods and the rules between them are as follows:") $$
           nest 2 (vcat (map showMeth uses))
         debugPath =
             s2par ("The execution order path is as follows:") $$
             nest 2 (s2par (intercalate " -> " (map ishow path))) $$
             s2par ("The relationships were introduced for the following " ++
                    "reasons:") $$
             nest 2 (vcat explanations)
    in
        intro $$ debugMeth $$ debugPath
   )
getErrorText (EDynamicExecOrderTwoRulesBothDir rule1 rule2 uses1 uses2) =
    (Generate 101, empty,
     let intro =
           s2par("The rules " ++ quote rule1 ++ " and " ++ quote rule2 ++
                 " require dynamic scheduling, which is not supported by " ++
                 "Bluesim.  This is because the rules use methods which " ++
                 "have a rule that executes between them in the static " ++
                 "execution order of the separately synthesized submodule, " ++
                 "but some pairs must execute in one order and some pairs " ++
                 "must execute in the opposite order.  " ++
                 "See entry #30 in the KPNS document for more information " ++
                 "and possible solutions.")
         showMeth (m1,m2,rs) =
             s2par ("(" ++ m1 ++ ", " ++ m2 ++ ")") $$
             nest 2 (sepList (map text rs) comma)
         debugMeth1 =
           s2par ("The methods and the rules between them which must " ++
                  "execute in the forward direction are as follows:") $$
           nest 2 (vcat (map showMeth uses1))
         debugMeth2 =
           s2par ("The methods and the rules between them which must " ++
                  "execute in the reverse direction are as follows:") $$
           nest 2 (vcat (map showMeth uses2))
    in
        intro $$ debugMeth1 $$ debugMeth2
   )

getErrorText (EInoutExprClockDomain port port_clkinfo expr_clkinfo) =
    (Generate 102, empty,
     let intro = s2par ("The value assigned to Inout module argument " ++
                        quote port ++ " is in the wrong clock domain.")
         port_msg =
           case (port_clkinfo) of
             Nothing ->
                 s2par ("The port was declared with no clock, " ++
                        "but the expression for the value has a clock.")
             Just (port_clknames, port_clks) ->
                 s2par ("Input/output clocks of the module " ++
                        "which are in the domain of the port:") $$
                 nest 2 (sepList (map text port_clknames) comma) $$
                 s2par ("Clocks connected to those inputs/outputs:") $$
                 nest 2 (sepList (map text port_clks) comma)
         arg_msg =
           case (expr_clkinfo) of
             Nothing ->
                 s2par ("The expression has no clock.")
             Just expr_clks ->
                 s2par ("Clocks of the expression:") $$
                 nest 2 (sepList (map text expr_clks) comma)
     in
         intro $$ port_msg $$ arg_msg
    )

getErrorText (WInoutExprReset port port_rst) =
    (Generate 103, empty,
     let intro =
           s2par ("The value assigned to Inout module argument " ++
                  quote port ++
                  " is influenced by a different reset signal than " ++
                  "expected by the module.")
         port_msg =
           s2par ("The reset expected by the module:") $$
           nest 2 (text port_rst)
     in
         intro $$ port_msg
    )

getErrorText (EModuleLoop name) =
    (Generate 104, empty,
     s2par ("Illegal recursive module reference while expanding " ++ name))

getErrorText (EPortKeywordClashFromMethod method port) =
    (Generate 105, empty,
     s2par ("Method " ++ quote method ++ " generates a port with name " ++
            quote port ++ " which clashes with a Verilog keyword."))
getErrorText (EPortNotValidIdentFromMethod method port) =
    (Generate 106, empty,
     s2par ("Method " ++ quote method ++ " generates a port with name " ++
            quote port ++ " which is not an accepted Verilog identifier.  " ++
            "It must contain only letters, digits, $ and _, " ++
            "but cannot begin with $ or a digit."))

getErrorText (EPortNamesClashArgAndIfc port arg meth methloc) =
    (Generate 107, empty,
     s2par
       ("Module argument " ++ quote arg ++
        " generates a port with name " ++ quote port ++
        " which conflicts with a port of the same name generated by method " ++
        quote meth ++ " at location " ++ prPosition methloc ++ "."))

getErrorText (EBSimSplitMethods meth_names) =
    (Generate 108, empty,
     s2par ("Bluesim does not currently support split methods at " ++
            "synthesis boundaries.  Consider not splitting the method " ++
            "or removing the synthesis boundary. " ++
            "This module has the following split methods:") <+>
     quoteStrList meth_names <> text ".")

getErrorText (EUndeterminedRules) =
    (Generate 109, empty,
     s2par ("Trying to generate rules from a don't-care value. " ++
            "Perhaps you meant to use " ++ quote "emptyRules" ++ "."))

getErrorText (EInvalidLogBase) =
    (Generate 110, empty,
     s2par ("A logarithm operator was applied to a non-positive base " ++
            "during elaboration."))
getErrorText (EInvalidLogOneOne) =
    (Generate 111, empty,
     s2par ("A logarithm operator of base 1 was applied to the value 1 " ++
            "during elaboration."))
getErrorText (ENegativeSqrt) =
    (Generate 112, empty,
     s2par ("A square-root operation was applied to a negative number " ++
            "during elaboration."))
getErrorText (EAddPosAndNegInfinity) =
    (Generate 113, empty,
     s2par ("An addition or subtraction operator attempted to combine " ++
            "positive and negative infinity during elaboration."))
getErrorText (EMultiplyZeroAndInfinity) =
    (Generate 114, empty,
     s2par ("A multiplication operator was applied to zero and infinity " ++
            "during elaboration."))

getErrorText (EFloatNaN) =
    (Generate 115, empty,
     s2par ("The $bitstoreal task cannot be used to create values which " ++
            "are not a number (NaN)."))

getErrorText (EDynamicExecOrderTwoRulesLoop path explanations) =
    (Generate 116, empty,
     let intro =
           s2par("This module requires dynamic scheduling, which is not " ++
                 "supported by Bluesim.  This is because there are two or " ++
                 "more pairs of rules which use methods which " ++
                 "have a rule that executes between them in the static " ++
                 "execution order of the separately synthesized submodule, " ++
                 "but, when these orderings are taken into account, " ++
                 "a loop results in the current module's schedule.  " ++
                 "See entry #30 in the KPNS document for more information " ++
                 "and possible solutions.")
         debugPath =
             s2par ("The ordering loop is as follows:") $$
             nest 2 (s2par (intercalate " -> " (map ishow path))) $$
             s2par ("The relationships were introduced for the following " ++
                    "reasons:") $$
             nest 2 (vcat explanations)
    in
        intro $$ debugPath
   )

getErrorText (WActionShadowing earlier_rule later_rule methods) =
   (Generate 117, empty,
    let intro = s2par ("Rule " ++ quote later_rule ++
                       " shadows the effects of " ++ quote earlier_rule ++
                       " when they execute in the same clock cycle. " ++
                       "Affected method calls:")
        outro = s2par ("To silence this warning, use the " ++
                       quote "-no-warn-action-shadowing" ++ " flag.")
    in  intro $$
        nest 2 (sepList (map text methods) comma) $$
        outro
   )

getErrorText EUseMissingDefaultClock =
   (Generate 118, empty, s2par ("This module specifies that it has no default clock " ++
                                "(with the no_default_clock attribute), " ++
                                "but attempted to use the missing default clock. " ++
                                "An instantiation may be missing clocked_by."))

getErrorText EUseMissingDefaultReset =
   (Generate 119, empty, s2par ("This module specifies that it has no default reset " ++
                                "(with the no_default_reset attribute), " ++
                                "but attempted to use the missing default reset. " ++
                                "An instantiation may be missing reset_by."))

getErrorText (EParamOnlyType arg_name arg_type) =
   (Generate 120, empty,
    s2par ("Module argument " ++ quote arg_name ++
           " is of type " ++ quote arg_type ++
           ", which is only supported on synthesis boundaries as a " ++
           "parameter and not a port. Either use the " ++ quote "parameter" ++
           " keyword or change the type of the argument."))

getErrorText(EVerilogFilterError fltr vlfile errcode) =
  (Generate 121, empty,
   s2par ("Verilog filter `" ++ fltr ++
          "' returned error code `" ++ show errcode ++ "' when run on generated verilog file `" ++ vlfile ++
         "'.")
   )

getErrorText(EInvalidWhen) =
  (Generate 122, empty,
   s2par ("The function " ++ quote "when" ++ " is being applied to an " ++
          "expression that cannot be lifted to a rule/method condition, " ++
          "either because it contains the result of an ActionValue call " ++
          "or because it is in a method and refers to a method argument.")
  )

getErrorText (WInlinedMethodIdAttribute name ) =
    (Generate 123, empty,
     s2par ("Ignoring reference to method " ++ quote name ++ ".  " ++
            "Scheduling attributes on inlined methods are not yet " ++
            "supported."))

getErrorText (EPortNameErrorOnImport mod port) =
  let extra = if (port == "RST")
              then " Port " ++ quote "RST_N" ++ " has been renamed to " ++ quote "RST" ++
                   " throughout Bluespec's Verilog library."
              else ""
  in (Generate 124, empty,
      s2par ("Cannot find a port named " ++ quote port ++
             " in the import of Verilog module named " ++ quote mod ++ "." ++
             " Check that the port names match between the Verilog and BVI." ++
             extra
            ))

getErrorText (EStringToChar str) =
    (Generate 125, empty,
     s2par ("Cannot convert string to character because the length != 1:") $$
     nest 2 (text (show str)))
getErrorText (EIntegerToChar n) =
    (Generate 126, empty,
     s2par ("Cannot convert the number " ++ itos n ++
            " to a character because it is out of range (0 - 255)."))

getErrorText (WMethodMultipleBoundaryReset meth m_reset) =
    (Generate 127, empty,
     s2par ("Reset information for method " ++ quote meth ++
            " is lost because it has multiple associated resets." ++
            case m_reset of
              Nothing -> ""
              Just rst -> " Instantiations will associate the method " ++
                          "with reset " ++ quote rst ++ "."
           ))

getErrorText (WRuleUndetPred is_meth rule poss) =
    (Generate 128, empty,
     let desc = if is_meth then "method" else "rule"
         intro = s2par ("The condition for " ++ desc ++ " " ++ quote rule ++
                        " contains a don't-care value.  " ++
                        "This may cause the condition to be undetermined.")
     in  if (null poss)
         then intro
         else intro $$
              s2par ("Don't-care values were introduced at the following positions:") $$
              nest 4 (vcat (map (text . prPosition) poss))
    )

getErrorText (EStringListNF s) =
    (Generate 129, empty, s2par ("Not a compile time string list: " ++ s))


---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- System errors ----------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

getErrorText (EMissingPackage p) =
    (System 0, empty, s2par ("Cannot find package " ++ ishow p))
getErrorText (WFilePackageNameMismatch fname pname) =
    (System 1, empty, s2par ("File name " ++ ishow fname ++ " does not match package name " ++ ishow pname))
-- Removed System 2 EFailOpenSrcFile. Obsoleted by EFileReadFailure.
getErrorText (EMissingBinFile fname package) =
    (System 3, empty, s2par ("Cannot find the binary file " ++ ishow fname ++ " for package " ++ ishow package))
getErrorText (EMissingIfcFile fname package) =
    (System 4, empty, s2par ("Cannot find the interface file " ++ ishow fname ++ " for package " ++ ishow package))
getErrorText (EBinFileVerMismatch fname) =
    (System 5, empty, s2par ("Binary version mismatch in " ++ ishow fname ++ ". Recompile!"))
getErrorText (ENoEntryPoint) =
    (System 6, empty, s2par ("No top-level module specified for simulation." ++
                             " Use flag ``-e'' to set the entry point."))
getErrorText (ECircularImports packages) =
    (System 7, empty, s2par ("Circular package importing: " ++ unwordsAnd packages))

getErrorText (EUnknownFlag flag) =
    (System 8, empty, s2par ("Unrecognized flag: " ++ flag))

getErrorText (EDupKillFlag newflag prevflag) =
    (System 9, empty, s2par ("Duplicate -KILL: " ++ newflag ++ " (earlier: " ++ prevflag ++ ")"))
getErrorText (ENotToggleFlag flag) =
    (System 10, empty, s2par ("The " ++ quote "-no" ++ " prefix is not allowed with the flag " ++ flag))
getErrorText (ENoArgFlag flag) =
    (System 11, empty, s2par ("The flag " ++ flag ++ " does not take an argument"))
getErrorText (EOneArgFlag flag) =
    (System 12, empty, s2par ("The flag " ++ flag ++ " requires an argument"))
getErrorText (ETwoArgFlag flag) =
    (System 13, empty, s2par ("The flag " ++ flag ++ " requires two arguments"))

getErrorText (ENoBackendCodeGen mods) =
    (System 14, empty, s2par ("You must specify -sim or -verilog to generate code for " ++ unwordsAnd (map ishow mods)))

-- This should be obsoleted
getErrorText (EGeneric s) =
    (System 15, empty, s2par s)

getErrorText (EUnknownSrcExt ext) =
    (System 16, empty, s2par ("Unrecognized extension " ++ ishow ext))
getErrorText (ENoSrcExt fname) =
    (System 17, empty, s2par ("Filename does not have a recognized Bluespec extension: " ++ ishow fname))
getErrorText (EFlagAfterSrc flag) =
    (System 18, empty, s2par ("Flags must appear before source files.  Found flag " ++ ishow flag))
getErrorText (ENotVerSrcFile fname) =
    (System 19, empty, s2par ("Filename does not have a recognized Verilog extension: " ++ ishow fname))
getErrorText (ENotCSrcFile fname) =
    (System 20, empty, s2par ("Filename does not have a recognized C extension: " ++ ishow fname))
-- Removed System 21 ENeedUpdCheckFlag, unsupported feature
getErrorText (EMultipleSrcFiles) =
    (System 22, empty, s2par ("Only one source file may be given at a time.  Use the " ++
                              quote "-u" ++ " flag to compile dependencies."))
getErrorText (WNoScheduleDump scheduler rules) =
    (System 23, empty, s2par ("Schedule dumps not correctly implemented for " ++ scheduler ++ " scheduler rules:")  $$
                               brackets (sepList (map text rules) comma))

getErrorText (EIntegerArgFlag flag) =
    (System 24, empty, s2par ("The flag " ++ flag ++ " requires an integer argument"))
getErrorText (EFloatArgFlag flag) =
    (System 25, empty, s2par ("The flag " ++ flag ++ " requires a numeric argument"))

getErrorText (EUnsupportedMutualRecursion ids) =
    (System 26, empty, s2par ("Local mutual recursion detected among the following identifiers: ") $$
                       brackets (sepList (map text ids) comma) $$
                       s2par ("This is currently unsupported."))
getErrorText (EBinFileSignatureMismatch pkgfile importer) =
    (System 27, empty,
     s2par ("The package " ++ quote importer ++ " was compiled using " ++
            "a different version of the file " ++ quote pkgfile
            ++ " than what was found in the path.") $$
     s2par ("Please recompile the affected packages in dependency order or with -u."))
getErrorText (WExperimental feature) =
    (System 28, empty,
     s2par ("Support for " ++ feature ++ " in this release is not complete or has not been tested"))
getErrorText (EMixedSrcFiles) =
    (System 29, empty,
     s2par ("Files for linking must be all Verilog files " ++
            "or all C files.  They cannot be mixed."))
getErrorText (EFileReadFailure filename err_descr) =
    (System 30, empty,
     s2par ("Could not read the file " ++ quote filename ++ ":") $$
     nest 2 (s2par err_descr))
getErrorText (EFileWriteFailure filename err_descr) =
    (System 31, empty,
     s2par ("Could not write the file " ++ quote filename ++ ":") $$
     nest 2 (s2par err_descr))
getErrorText (EDirCreateFailure dirname err_descr) =
    (System 32, empty,
     s2par ("Could not create the directory " ++ quote dirname ++ ":") $$
     nest 2 (s2par err_descr))
getErrorText (EBSimMCDUnsupported feature) =
    (System 33, empty,
     s2par ("This design uses the MCD feature '" ++ feature ++ "' which is not currently supported by Bluesim."))
getErrorText (EMissingIncludeFile fname) =
    (System 34, empty,
     s2par ("Cannot find the file " ++ ishow fname ++ " to be included"))
getErrorText (EUnknownVerilogSim "" good_sims True) =
    (System 35, empty,
     s2par ("No supported Verilog simulator found; supported simulators:") $+$
     nest 2 (sepList (map (text . ishow) good_sims) comma))
getErrorText (EUnknownVerilogSim bad_sim good_sims True) =
    (System 35, empty,
     s2par ("Unsupported Verilog simulator " ++ ishow bad_sim ++
            "; supported simulators:") $+$
     nest 2 (sepList (map (text . ishow) good_sims) comma))
getErrorText (EUnknownVerilogSim "" good_sims False) =
    (System 35, empty,
     s2par ("No supported Verilog post-processors found; supported post-processors:") $+$
     nest 2 (sepList (map (text . ishow) good_sims) comma))
getErrorText (EUnknownVerilogSim bad_sim good_sims False) =
    (System 35, empty,
     s2par ("Unsupported Verilog post-processor " ++ ishow bad_sim ++
            "; supported post-processors:") $+$
     nest 2 (sepList (map (text . ishow) good_sims) comma))
getErrorText (EBadArgFlag flag found valids) =
    (System 36, empty,
     s2par ("The flag " ++ flag ++ " does not accept " ++ quote found ++
            " as an argument. " ++ "Valid arguments are: ") <+>
     quoteStrList valids <> text "."
     )
getErrorText (EUnrecognizedCmdLineText str) =
    (System 37, empty,
     s2par ("Unrecognized text on the command line: " ++ str))

getErrorText (ETooManyBackends) =
    (System 38, empty,
     s2par ("Only one backend can be specified for code generation.  " ++
            "Please choose between -sim and -verilog."))
getErrorText (WExtraABinFiles filenames) =
    (System 39, empty,
     s2par ("The following elaboration files were not used in the design:") $$
     nest 2 (sepList (map text filenames) comma))
getErrorText (EMissingABinModFile module_name mparent) =
    (System 40, empty,
     case (mparent) of
         Nothing ->
             s2par ("No elaboration file (.ba) was found for " ++
                    "the top-level module " ++ ishow module_name ++ ".")
         Just parent_name ->
             s2par ("No elaboration file (.ba) was found for " ++
                    "the module " ++ ishow module_name ++ " instantiated " ++
                    "by the module " ++ ishow parent_name ++ ".")
     )
getErrorText (EMultipleABinFilesForName lookup_name filenames) =
    (System 41, empty,
     s2par ("Multiple elaboration files (.ba) found for " ++
            ishow lookup_name ++ ":") $$
     nest 2 (sepList (map text filenames) comma))
getErrorText (EABinFileBackendMismatch
                  filename expected_backend found_backend) =
    (System 42, empty,
     s2par ("Backend mismatch for file " ++ ishow filename ++ ". " ++
            "The file was compiled for the " ++ found_backend ++
            " backend, while the current compilation is for the " ++
            expected_backend ++ " backend."))
getErrorText (EBluesimNoXZ target_value) =
    (System 43, empty,
     s2par ("Bluesim does not support '" ++ target_value ++
            "' for undetermined values -- use '0', '1' or 'A' instead."))
getErrorText (EWrongBackend source_backend flag_backend) =
    (System 44, empty,
     s2par ("The chosen back end does not match the source files.  " ++
            "The files for linking are for the " ++ source_backend ++
            " back end, but the " ++ flag_backend ++
            " back end was specified."))
getErrorText (EMissingUserFile filename path) =
    let path_str = intercalate ":" path
    in (System 45, empty, s2par ("Unable to read file " ++ ishow filename ++ " using the path " ++ path_str))

getErrorText (EMissingABinForeignFuncFile ffunc_name using_module) =
    (System 46, empty,
     s2par ("No elaboration file (.ba) was provided for " ++
            "the foreign function " ++ ishow ffunc_name ++
            " used in the module " ++ ishow using_module ++ ".")
     )
getErrorText (EWrongABinTypeExpectedModule module_name mparent) =
    (System 47, empty,
     let hdr = s2par ("The elaboration file (.ba) provided for " ++
                      ishow module_name ++ " is not of the correct type.")
     in case (mparent) of
          Nothing ->
             hdr <+> s2par ("The file is for a foreign function but " ++
                            ishow module_name ++ " was identified as the " ++
                            "top-level module.")
          Just parent_name ->
             hdr <+> s2par ("The file is for a foreign function but " ++
                            ishow module_name ++
                            " is instantiated as a module by the module " ++
                            ishow parent_name ++ ".")
     )
getErrorText (EWrongABinTypeExpectedForeignFunc ffunc_name parent_name) =
    (System 48, empty,
     s2par ("The elaboration file (.ba) provided for " ++
            ishow ffunc_name ++ " is not of the correct type.  " ++
            "The file is for a module but " ++
            ishow ffunc_name ++ " is called as a foreign function" ++
            (if null parent_name
             then "."
             else " in the module " ++ ishow parent_name ++ "."))
    )

getErrorText (ENoBackendLinking) =
    (System 49, empty,
     s2par ("You must specify -sim or -verilog for linking."))

getErrorText (ELinkFilesWithSrc src_name link_names) =
    (System 50, empty,
     let file_list = if (length link_names > 3)
                     then (take 3 link_names) ++ ["..."]
                     else link_names
     in  s2par ("Source files and link files cannot be specified together. " ++
                "Found the source file " ++ quote src_name ++
                " with the following link files:") <+>
         sepList (map text file_list) comma
    )

getErrorText (EVerilogFilesWithSimBackend vnames) =
    (System 51, empty,
     s2par ("Verilog files are not expected for Bluesim linking:") $+$
     nest 2 (sepList (map text vnames) comma))

getErrorText (EVPIFilesWithNoABin vpinames) =
    (System 52, empty,
     s2par ("Elaboration files (.ba) must be provided for any " ++
            "imported foreign functions:") $+$
     nest 2 (sepList (map text vpinames) comma))

getErrorText (EGenNamesForLinking names) =
    (System 53, empty,
     s2par ("The -g flag only applies to Bluespec source files."))

getErrorText (EEntryForCodeGen names) =
    (System 54, empty,
     s2par ("The -e flag does not apply to Bluespec source files."))

-- Removed System 55, EBluesimBadCxxFamily -- only support one platform in dir tree

getErrorText EDollarNoVerilog =
    (System 56, empty,
     s2par ("The flag -remove-dollar is only supported for -verilog."))

getErrorText EDollarLink =
    (System 57, empty,
     s2par ("The flag -remove-dollar in only supported for compiling source, not linking."))

-- Removed System 58 ELicenseUnavailable, BSC is now open source
-- Removed System 59 WLicenseExpires, BSC is now open source
-- Removed System 60 WWaitForLicense, BSC is now open source
-- Removed Sysetm 61 WLicenseSearchPath, BSC is now open source

getErrorText (WDeprecatedFlag flag message) =
    (System 62, empty,
     s2par ("Deprecated flag \"-" ++ flag ++ "\". " ++ message))

getErrorText (ESystemCWrapperComboPaths path_desc) =
    (System 63, empty,
     s2par ("Generation of a SystemC model requires that the top-level " ++
            "interface have no combinational paths, but the requested model " ++
            "does have combinational paths from inputs to outputs.") $+$
     (text "") $+$ (text path_desc))

getErrorText (ESystemCWrapperInvalidMethods methods) =
    (System 64, empty,
     s2par ("Generation of a SystemC model restricts the top-level " ++
            "interface to only Action methods and value methods with no " ++
            "arguments.  SystemC model generation is not supported for " ++
            "the following methods:") $+$
     nest 2 (sepList (map text methods) comma))

getErrorText (EABinNameMismatch lookup_name filename filemodname) =
    (System 65, empty,
     s2par ("A search for the elaboration file (.ba) for module " ++
            ishow lookup_name ++ " found the following file:") $$
     nest 2 (text filename) $$
     s2par ("However, this file is for module " ++ ishow filemodname ++
            ".  Please rename this file, adjust the search path, or " ++
            "provide the correct elaboration file on the command line."))

getErrorText (EMutualRecursionComplicatedClause d) =
    (System 66, empty,
     s2par ("Unable to process local mutual recursion of '" ++
            d ++ "' due to function " ++
            "arguments, patterns, or qualifiers.  " ++
            "Perhaps you may rewrite definitions of the form") $$
            nest 2 (s2par "f x = y") $$
                 s2par "into" $$
            nest 2 (s2par "f = let { temp x = y } in temp"))
    -- But rewriting is not so helpful of a suggestion if
    -- this is coming from internally generated code.

getErrorText (ESystemCWrapperRuleBeforeMethod methods) =
    (System 67, empty,
     s2par ("Generation of a SystemC model requires that the top-level " ++
            "value methods have no rules or methods which must schedule " ++
            "or execute before them.  SystemC model generation is not " ++
            "supported for the following methods:") $+$
     nest 2 (sepList [ m <+> (text "because it") <+> reason
                     | (m,reason) <- methods
                     ]
                     comma))

getErrorText (EExactlyOneArgRequired desc []) =
    (System 68, empty,
     s2par ("You must supply exactly one " ++ desc ++
            ", but none were provided"))
getErrorText (EExactlyOneArgRequired desc args) =
    (System 68, empty,
     s2par ("You must supply exactly one " ++ desc ++
            ", but multiple were provided:") $$
     nest 2 (sepList (map text args) comma))

getErrorText (EFloatingPointNotIEEE) =
    (System 69, empty,
     s2par ("This computer does not implement floating point numbers " ++
            "according to the IEEE standard.  This is required for " ++
            "floating point support."))

getErrorText (EFloatingPointRadixNotTwo) =
    (System 70, empty,
     s2par ("The floating point number implementation on this computer " ++
            "does not use a radix of 2.  This is required for floating " ++
            "point support."))

getErrorText (EFloatingPointPrecisionNot53) =
    (System 71, empty,
     s2par ("The floating point number implementation on this computer " ++
            "does not use a precision of 53 bits.  This is required for " ++
            " floating point support."))

getErrorText (EDoubleNot64Bit) =
    (System 72, empty,
     s2par ("The size of floating point `double' on this computer is not " ++
            "64 bits.  This is required for floating point support."))

getErrorText (WDuplicatePathDirs pathName flagName dupDir dirs) =
    (System 73, empty,
     let msg = s2par ("Duplicate directories were found in the path " ++
                      "specified with the -" ++ pathName ++ " flag.  Only the first " ++
                      "occurrence will be used.  The duplicates are:") $$
               nest 2 (vcat (map text dirs))
         dir_msg = s2par ("Note that when the -" ++ flagName ++ " flag is used, that " ++
                          "directory is automatically added to the head " ++
                          "of the path.")
     in  msg $$ if dupDir then dir_msg else empty
    )

getErrorText (EForeignModSynth name) =
    (System 74, empty,
     s2par ("Import BVI module " ++ quote name ++
            " cannot be selected for synthesis."))

getErrorText (ENoOptUndetNoXZ target_value) =
    (System 75, empty,
     s2par ("When the -opt-undetermined-vals flag is off, " ++
            "'" ++ target_value ++ "' for undetermined values is not " ++
            "supported -- use '0', '1' or 'A' instead."))

getErrorText (EABinModSchedErr module_name mparent) =
    (System 76, empty,
     let hdr = s2par ("The elaboration file (.ba) provided for " ++
                      ishow module_name ++ " indicates that a scheduling " ++
                      "error occurred during compilation.")
     in case (mparent) of
          Nothing -> hdr -- The context does not allow error modules
          Just parent_name ->
             hdr <+> s2par ("A top module with an error can be loaded, " ++
                            "to permit debugging of that module. Child " ++
                            "modules with errors cannot be loaded. This " ++
                            "module was instantiated as a child of the " ++
                            "module " ++ ishow parent_name ++ ".")
     )
getErrorText (MRestrictions section feature) =
    (System 77, empty,
     s2par ("Please refer to the section on " ++ section ++
            " in the Bluespec User Guide for restrictions on using " ++ feature ++ "."))

getErrorText (EBinFileSignatureMismatch2 pkgfile importer1 importer2) =
    (System 78, empty,
     s2par ("The packages " ++ quote importer1 ++ " and " ++ quote importer2 ++
            " were compiled with different versions of the file " ++
            quote pkgfile ++ ".") $$
     s2par ("Please recompile the affected packages in dependency order or with -u."))

-- Removed System 79 ELicenseElabLimit, BSC is open source

getErrorText (WSuppressedWarnings count) =
  (System 80, empty,
   s2par (itos count ++ " warnings were suppressed."))

getErrorText (WSATNotAvailable flagstr libname m_dflt_sat) =
  (System 81, empty,
   s2par ("The flag " ++ quote flagstr ++
          " was used, but a proper shared object file was not found. " ++
          "Please specify a different SAT solver or check that the " ++
          "LD_LIBRARY_PATH or BLUESPEC_LD_LIBRARY_PATH includes a valid " ++
          quote libname ++ " file." ++
          (case (m_dflt_sat) of
             Nothing -> ""
             Just dflt_sat ->
               " The `" ++ dflt_sat ++ "' behavior will be used."
          )
         )
   )

getErrorText (ECircularImportsViaBinFile srcPkg impPkg) =
    (System 82, empty,
     s2par ("Circular package importing: The package " ++ quote srcPkg ++
            " imports " ++ quote impPkg ++ ", which was pre-compiled " ++
            "with an import of " ++ quote srcPkg ++ ".  " ++
            "Perhaps there is a name conflict between a source package " ++
            "and a pre-compiled library package."))

getErrorText (EPositiveIntegerArgFlag flag) =
    (System 83, empty,
     s2par ("The flag " ++ flag ++ " requires a positive integer argument"))

getErrorText (EFileRemoveFailure filename err_descr) =
    (System 84, empty,
     s2par ("Could not remove the file " ++ quote filename ++ ":") $$
     nest 2 (s2par err_descr))

getErrorText (EFileHandleFailure err_descr) =
    (System 85, empty,
     s2par ("Failure during a file handle operation:") $$
     nest 2 (s2par err_descr))

getErrorText (EFileCopyFailure src dst err_descr) =
    (System 86, empty,
     s2par ("Could not copy " ++ quote src ++ " to " ++ quote dst ++ ":") $$
     nest 2 (s2par err_descr))

getErrorText (ECircularABin topmod insts) =
    (System 87, empty,
     let ppInst (mod, inst) = s2par("Module " ++ quote mod ++
                                    " instantiated as " ++ quote inst)
     in  s2par ("Circular module hierarchy detected in the elaboration " ++
                "files (.ba) for this design. The module " ++ quote topmod ++
                " instantiates itself through the following hierarchy:") $$
         nest 2 (vcatList (map ppInst insts) comma))

getErrorText (WFileExistsButUnreadable fname err_descr) =
    (System 88, empty,
     s2par ("Found but could not read the file " ++ quote fname ++ ":") $$
     nest 2 (s2par err_descr))

getErrorText (WMultipleFilesInPath chosen_fname other_fnames) =
    (System 89, empty,
     s2par ("Multiple copies of a file were found in the path. " ++
            "Using:") $$
     nest 2 (text chosen_fname) $$
     s2par ("Ignoring:") $$
     nest 2 (vcat (map text other_fnames)))

getErrorText (EBinFilePkgNameMismatch filename exp_name found_name) =
    (System 90, empty,
     s2par ("Expected to find package " ++ quote exp_name ++ " in the file " ++
            quote filename ++ ", found " ++ quote found_name ++ "."))

getErrorText (WOpenPathDirFailure pathName dir msg) =
    (System 91, empty,
     s2par ("Removing a directory from the path specified with the -" ++
            pathName ++ " flag, because it could not be opened.") $$
     s2par ("Directory:") $$
     nest 2 (text dir) $$
     s2par ("System message:") $$
     nest 2 (text msg))

getErrorText (EOpenOutputDirFailure dirFlag dir msg) =
    (System 92, empty,
     s2par ("Could not open the directory specified with the -" ++
            dirFlag ++ " flag.") $$
     s2par ("Directory:") $$
     nest 2 (text dir) $$
     s2par ("System message:") $$
     nest 2 (text msg))

getErrorText (EMsgListArgFlag flag found) =
    (System 93, empty,
     s2par ("The flag " ++ flag ++ " does not accept " ++ quote found ++
            " as an argument. Valid arguments are `ALL', `NONE', " ++
            "or a colon-separated list of message tags."))

getErrorText (WNonDemotableErrors tags) =
    (System 94, empty,
     let s = if (length tags == 1) then "" else "s"
     in  s2par ("Cannot demote the following error" ++ s ++ ":") $$
         nest 2 (sepList (map text tags) comma))

getErrorText (EMissingVPIWrapperFile fname is_dpi) =
    (System 95, empty,
     let ifctype = if is_dpi then "DPI" else "VPI"
     in  s2par ("Cannot find the " ++ ifctype ++ " file " ++ ishow fname ++
                " in the Verilog search path."))

-- Runtime errors
getErrorText (EMutuallyExclusiveRulesFire r1 r2) =
    (Runtime 1, empty,
     s2par ("Mutually exclusive rules (from the ME sets " ++ r1 ++ " and " ++ r2 ++ ") fired in the same clock cycle."))

-- If all the errors are covered, then this line causes the compiler
-- to give an overlap warning.  Thus, the OPTIONS pragma on this file.
-- getErrorText err = internalError ("Missing error message: " ++ show err)

getErrorText (EConflictFreeRulesFail (r1, r2) o (m1, m2)) =
   (Runtime 2, empty,
    s2par ("Conflict-free rules " ++ r1 ++ " and " ++ r2 ++
           " called conflicting methods " ++ m1 ++ " and " ++ m2 ++
           " of module instance " ++ o ++ "."))

-- -----

ishow :: String -> String
ishow s = quote s

quoteStrList :: [String] -> Doc
quoteStrList ss = sep (punctuate comma (map (text . quote) ss))

dropping :: String
dropping = " Removing..."

missingEndKeywordSuggestion :: Maybe String -> String
missingEndKeywordSuggestion Nothing = ""
missingEndKeywordSuggestion (Just kw) =
    ".  Perhaps " ++ quote kw ++ " is missing?"

-- -----

prMethodsByClockDomain :: [[(String, [(String, Position)])]] -> Doc
prMethodsByClockDomain clock_domains =
     s2par ("Method calls by clock domain:") $$
     nest 2 (sep (map pDom (zip ([1..] :: [Integer]) clock_domains)))
  where pDom (n, clocks) = s2par ("Clock domain " ++ (itos n) ++ ":") $$
                           nest 2 (sep (map pClk clocks))
        pClk (c, methods) = text (c ++ ":") $$
                            nest 2 (sep (map pMeth methods))
        pMeth (s, pos) =
            text s <+>
            if (isUsefulPosition pos)
              then text ("at") <+> text (prPosition pos) <> comma
              else empty

prMethodsByReset :: [(String, [(String, Position)])] -> Doc
prMethodsByReset reset_list =
     s2par ("Method calls by reset:") $$
     nest 2 (sep (map pRst (zip ([1..] :: [Integer]) reset_list)))
  where pRst (n, (rst_name, method_calls)) =
            s2par ("Reset " ++ (itos n) ++ " (" ++ rst_name ++ "):") $$
            nest 2 (sep (map pMeth method_calls))
        pMeth (s, pos) =
            text s <+>
            if (isUsefulPosition pos)
              then text ("at") <+> text (prPosition pos) <> comma
              else empty

-- -------------------------
