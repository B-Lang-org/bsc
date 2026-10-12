module WaveCheck ( FileNum, file1, file2
                , CheckCmd, parseCheckCmd
                , checkStream
                ) where

-- Waveform assertion checking over the VCD command representation.
--
-- This is the engine behind the vcdcheck and fstcheck utilities: it
-- consumes a stream of VCDCmds (parsed from VCD text, or converted
-- from an FST file by FSTRead) and runs the checkers given with -c.

import Error(internalError)
import VCD

import Data.List(intercalate, isPrefixOf)
import Data.Maybe(fromMaybe, isJust, isNothing)
import Data.Bits(shiftL, xor, (.|.), shiftR)
import Numeric(readDec, readHex)

import qualified Data.Map as M
import qualified Data.Set as S

-- -------------------------------------------------------------------
-- -------------------------------------------------------------------
-- Description of checker commands

-- Identify which file the command applies to
type FileNum = Int

file1, file2 :: FileNum
file1 = 1
file2 = 2

-- String describing which signals a command applies to
-- For now this is just a name, but may become a regex in the future
type SigSpec = String

-- Description of what time period a command applies to.
data TimeSpec = Initially
              | At Integer
              | Earlier Integer
              | Later Integer
              | Sometime
  deriving (Eq, Show)

-- increment time
incrTime :: Integer -> TimeSpec -> TimeSpec
incrTime t (At x) = At (t+x)
incrTime _ x = x

-- check the timespec against the current time
timeOK :: TimeSpec -> Integer -> Bool
timeOK Initially 0   = True
timeOK (At t) n      = t == n
timeOK (Earlier t) n = n < t
timeOK (Later t) n   = n > t
timeOK Sometime _    = True
timeOK _ _           = False

-- These are the supported checker commands
data CheckCmd = Exists SigSpec FileNum
              | Toggles SigSpec FileNum TimeSpec
              | Stable SigSpec FileNum TimeSpec
              | Value SigSpec Integer FileNum TimeSpec
              | IsX SigSpec FileNum TimeSpec
              | IsZ SigSpec FileNum TimeSpec
              | Matches SigSpec SigSpec TimeSpec
              | HasTimescale Integer Integer FileNum
              | GoesTo Integer FileNum
              | Sequence SeqCmd
  deriving (Show)

data SeqState = Waiting | Running | Finished
   deriving(Show, Eq)

-- Sequence to track a
data SeqCmd = CRCCmd
    {sc_fileNum  :: FileNum
    ,sc_signal   :: SigSpec
    ,sc_width    :: Integer
    ,sc_startVal :: Integer
    ,sc_nextTime :: TimeSpec
    ,sc_timeIncr :: TimeSpec
    ,sc_count    :: Integer
    ,sc_currentCount :: Integer
    ,sc_state    :: SeqState
    ,sc_crcfunction :: Integer -> Integer
    }

-- Show is used in properties -- only invariants are shown
instance Show SeqCmd where
    show c = "CRC: " ++ (sc_signal c)
             ++ " starting " ++ (show $ sc_startVal c)
             ++ " every " ++ (show $ sc_timeIncr c)
             ++ " for " ++ (show $ sc_count c)


-- Command parsing routines
data Target = IntVal Integer
            | XVal
            | ZVal
  deriving (Eq)

parseValue :: String -> Maybe Target
parseValue "false" = Just (IntVal 0)
parseValue "true"  = Just (IntVal 1)
parseValue "x"     = Just XVal
parseValue s | "'h" `isPrefixOf` s =
                 case (readHex (drop 2 s)) of
                   [(n,"")] -> Just (IntVal n)
                   _        -> Nothing
parseValue s = case (readDec s) of
                 [(n,"")] -> Just (IntVal n)
                 _        -> Nothing

parseTimeSpec :: String -> Maybe TimeSpec
parseTimeSpec "initially" = Just Initially
parseTimeSpec "sometime"  = Just Sometime
parseTimeSpec ('@':s)     = case (readDec s) of
                              [(t,"")] -> Just (At t)
                              _        -> Nothing
parseTimeSpec ('<':s)     = case (readDec s) of
                              [(t,"")] -> Just (Earlier t)
                              _        -> Nothing
parseTimeSpec ('>':s)     = case (readDec s) of
                              [(t,"")] -> Just (Later t)
                              _        -> Nothing
parseTimeSpec _ = Nothing

parseInteger :: String -> Maybe Integer
parseInteger s = case (readDec s) of
                   [(n,"")] -> Just n
                   _        -> Nothing

parseCheckCmd :: [FileNum] -> String -> [Either String CheckCmd]
parseCheckCmd fnums s = parse (words s)
  where parse :: [String] -> [Either String CheckCmd]
        parse [sig,"exists"]  =
            [ Right (Exists sig f) | f <- fnums ]
        parse [sig,"toggles"] =
            [ Right (Toggles sig f Sometime) | f <- fnums ]
        parse [sig,"toggles", t] =
            case (parseTimeSpec t) of
              (Just ts) ->
                  [ Right (Toggles sig f ts) | f <- fnums ]
              _ -> [Left s]
        parse [sig,"stable", t] =
            case (parseTimeSpec t) of
              (Just ts) ->
                  [ Right (Stable sig f ts) | f <- fnums ]
              _ -> [Left s]
        parse [sig,"equals",val,t] =
            case (parseValue val, parseTimeSpec t) of
              (Just v, Just ts) ->
                  case v of
                    (IntVal n) -> [ Right (Value sig n f ts) | f <- fnums ]
                    XVal       -> [ Right (IsX sig f ts) | f <- fnums ]
                    ZVal       -> [ Right (IsZ sig f ts) | f <- fnums ]
              _ -> [Left s]
        parse [sig,"becomes",val,t] =
            case (parseValue val, parseTimeSpec t) of
              (Just v, Just ts) ->
                  [ Right (Toggles sig f ts) | f <- fnums ] ++
                  case v of
                    (IntVal n) -> [ Right (Value sig n f ts) | f <- fnums ]
                    XVal       -> [ Right (IsX sig f ts) | f <- fnums ]
                    ZVal       -> [ Right (IsZ sig f ts) | f <- fnums ]
              _ -> [Left s]
        parse [sig,"remains",val,t] =
            case (parseValue val, parseTimeSpec t) of
              (Just v, Just ts) ->
                  [ Right (Stable sig f ts) | f <- fnums ] ++
                  case v of
                    (IntVal n) -> [ Right (Value sig n f ts) | f <- fnums ]
                    XVal       -> [ Right (IsX sig f ts) | f <- fnums ]
                    ZVal       -> [ Right (IsZ sig f ts) | f <- fnums ]
              _ -> [Left s]
        parse ["CRC", sig, startv, every, for] =
            case (parseValue startv, parseTimeSpec every, parseInteger for) of
              (Just (IntVal sv), Just et, Just fr) ->
                  let cmd = CRCCmd {sc_fileNum=0
                                   ,sc_signal=sig
                                   ,sc_width=0
                                   ,sc_startVal=sv
                                   ,sc_nextTime=Sometime
                                   ,sc_timeIncr=et
                                   ,sc_count=fr
                                   ,sc_currentCount = 0
                                   ,sc_state = Waiting
                                   ,sc_crcfunction = id}
                  in [Right (Sequence cmd{sc_fileNum=f}) | f <- fnums]
              (Nothing, _, _) -> [Left $ "Error in scanning CRC command -- start value " ++ startv]
              (_, Nothing, _) -> [Left $ "Error in scanning CRC command -- every time " ++ every]
              (_, _, Nothing) -> [Left $ "Error in scanning CRC command -- sequence length " ++ for]
              _                -> [Left $ "Error in scanning CRC command " ++ s]
        parse ("CRC":_) = [Left $ "CRC command expects 4 arguments " ++ s]
        parse _ = [Left s]


-- Routines for converting checker commands into checker functions

getFile :: CheckerState -> FileNum -> FilePath
getFile cs 1 = name (state1 cs)
getFile cs 2 = name (state2 cs)
getFile _  n = internalError $ "Bad file number: " ++ (show n)

cmdToCheckers :: CheckCmd -> [Checker]
cmdToCheckers cmd@(Exists sig fnum) =
    let prop = show cmd
        mkMsg cs = sig ++ " not found in " ++ (getFile cs fnum)
    in [ \_  -> OnDef fnum sig (const [set_prop prop])
       , \cs -> EndDef fnum (require_prop prop (mkMsg cs))
       ]
cmdToCheckers cmd@(Toggles sig fnum Sometime) =
    let prop_aux = show (Exists sig fnum)
        mkMsg_aux cs = sig ++ " not found in " ++ (getFile cs fnum)
        prop = show cmd
        mkMsg cs = sig ++ " never toggled in " ++ (getFile cs fnum)
        setup_checkers (code,_) =
            [ \_  -> Watch fnum code (set_prop_if_changed code fnum prop)
            , \cs -> EndVCD fnum (require_prop prop (mkMsg cs))
            ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_aux])
       , \cs -> EndDef fnum (require_prop prop_aux (mkMsg_aux cs))
       ]
cmdToCheckers cmd@(Toggles sig fnum (At t)) =
    let prop_aux = show (Exists sig fnum)
        mkMsg_aux cs = sig ++ " not found in " ++ (getFile cs fnum)
        mkMsg cs = sig ++ " did not toggle at " ++ (show t) ++ " in " ++ (getFile cs fnum)
        setup_checkers (code,_) =
            [ \cs  -> Wait t (check_toggle code fnum t (mkMsg cs)) ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_aux])
       , \cs -> EndDef fnum (require_prop prop_aux (mkMsg_aux cs))
       ]
cmdToCheckers cmd@(Stable sig fnum (At t)) =
    let prop_aux = show (Exists sig fnum)
        mkMsg_aux cs = sig ++ " not found in " ++ (getFile cs fnum)
        mkMsg cs = sig ++ " is not stable at " ++ (show t) ++ " in " ++ (getFile cs fnum)
        setup_checkers (code,_) =
            [ \cs  -> Wait t (check_stable code fnum t (mkMsg cs)) ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_aux])
       , \cs -> EndDef fnum (require_prop prop_aux (mkMsg_aux cs))
       ]
cmdToCheckers cmd@(Value sig val fnum (At t)) =
    let prop_aux = show (Exists sig fnum)
        mkMsg_aux cs = sig ++ " not found in " ++ (getFile cs fnum)
        mkMsg cs = sig ++ " != " ++ (show val) ++ " at " ++ (show t) ++ " in " ++ (getFile cs fnum)
        setup_checkers (code,_) =
            [ \cs  -> Wait t (check_value code fnum t val (mkMsg cs)) ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_aux])
       , \cs -> EndDef fnum (require_prop prop_aux (mkMsg_aux cs))
       ]
cmdToCheckers cmd@(IsX sig fnum (At t)) =
    let prop_aux = show (Exists sig fnum)
        mkMsg_aux cs = sig ++ " not found in " ++ (getFile cs fnum)
        mkMsg cs = sig ++ " != X at " ++ (show t) ++ " in " ++ (getFile cs fnum)
        setup_checkers (code,_) =
            [ \cs  -> Wait t (check_X code fnum t (mkMsg cs)) ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_aux])
       , \cs -> EndDef fnum (require_prop prop_aux (mkMsg_aux cs))
       ]
cmdToCheckers cmd@(IsZ sig fnum (At t)) =
    let prop_aux = show (Exists sig fnum)
        mkMsg_aux cs = sig ++ " not found in " ++ (getFile cs fnum)
        mkMsg cs = sig ++ " != Z at " ++ (show t) ++ " in " ++ (getFile cs fnum)
        setup_checkers (code,_) =
            [ \cs  -> Wait t (check_Z code fnum t (mkMsg cs)) ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_aux])
       , \cs -> EndDef fnum (require_prop prop_aux (mkMsg_aux cs))
       ]
cmdToCheckers (Sequence cmd) =
    let  fnum = sc_fileNum cmd
         sig = sc_signal cmd
         prop_exists = show (Exists sig fnum)
         mkMsg_exists cs = sig ++ " not found in " ++ (getFile cs fnum)
         --
         prop_started = show cmd ++ " Started"
         prop_complete = show cmd ++ " Completed"
         failed a = (show cmd) ++ " failed to " ++ a
         setup_checkers (code,width) =
             let cmd' = cmd {sc_width = width
                            ,sc_crcfunction = (crcFunction width)}
             in [
              \cs -> EndDef fnum (setup_crc code fnum cmd')
             ,\cs -> Watch fnum code (check_crc code fnum)
             ,\cs -> EndVCD fnum (require_prop prop_started (failed "start"))
             ,\cs -> EndVCD fnum (require_prop prop_complete (failed "complete"))
             ]
    in [ \_  -> OnDef fnum sig setup_checkers
       , \_  -> OnDef fnum sig (const [set_prop prop_exists])
       , \cs ->  EndDef fnum (require_prop prop_exists (mkMsg_exists cs))
       ]
cmdToCheckers cmd = [ failure $ "Not implemented: " ++ (show cmd)]

-- -------------------------------------------------------------------
-- Facility for managing checkers

type ValueMap = M.Map Code VCDValue

type Checker = CheckerState -> Action

type Property = String

data Action = Succeed
            | Fail String
            | SetProperty Property Checker
            | OnDef FileNum String ( (Code,Integer) -> [Checker])
            | EndDef FileNum Checker
            | Wait Integer Checker
            | Watch FileNum Code Checker
            | EndVCD FileNum Checker
            | UpdateCS Code FileNum SeqCmd Checker

data CheckerState = CS { props    :: S.Set Property
                       , waiting  :: M.Map Integer [Checker]
                       , user     :: M.Map (FileNum,Code) SeqCmd
                       , state1   :: FileState
                       , state2   :: FileState
                       }

data FileState = FS { name     :: FilePath
                    , scope    :: [String]
                    , stable   :: ValueMap
                    , changing :: ValueMap
                    , ondefs   :: M.Map String [ (Code,Integer) -> [Checker]]
                    , enddefs  :: [Checker]
                    , watching :: M.Map Code [Checker]
                    , endvcd   :: [Checker]
                    , now      :: Integer
                    }

getFS :: FileNum -> CheckerState -> FileState
getFS 1 = state1
getFS 2 = state2
getFS n = internalError $ "Bad file number: " ++ (show n)

setFS :: FileNum -> FileState -> CheckerState -> CheckerState
setFS 1 fs cs = cs { state1 = fs }
setFS 2 fs cs = cs { state2 = fs }
setFS n _  _  = internalError $ "Bad file number: " ++ (show n)

-- basic checkers

success :: Checker
success = const Succeed

failure :: String -> Checker
failure msg = const (Fail msg)

set_prop :: Property -> Checker
set_prop p = const $ SetProperty p success

require_prop :: Property -> String -> Checker
require_prop p msg = \cs -> if (p `S.member` (props cs))
                            then Succeed
                            else Fail msg

set_prop_if_changed :: Code -> FileNum -> Property -> Checker
set_prop_if_changed code fnum prop =
    \cs -> let fs = getFS fnum cs
               stable_val = M.lookup code (stable fs)
               changed_val = M.lookup code (changing fs)
               ok = (isJust changed_val) && (isJust stable_val) &&
                    (changed_val /= stable_val)
           in if ok
              then SetProperty prop success
              else Succeed  -- try again on next change

check_value :: Code -> FileNum -> Integer -> Integer -> String -> Checker
check_value code fnum t val msg =
    \cs -> let fs = getFS fnum cs
               stable_val = M.lookup code (stable fs)
               changed_val = M.lookup code (changing fs)
               stable_ok = maybe False (\v -> vcd_to_integer v == (Just val)) stable_val
               no_change = isNothing changed_val
               change_ok = maybe False (\v -> vcd_to_integer v == (Just val)) changed_val
               ok = if (now fs < t)
                    then stable_ok
                    else (stable_ok && no_change) || change_ok
           in if ok
              then Succeed
              else Fail msg

check_toggle :: Code -> FileNum -> Integer -> String -> Checker
check_toggle code fnum t msg =
    \cs -> let fs = getFS fnum cs
               stable_val = M.lookup code (stable fs)
               changed_val = M.lookup code (changing fs)
               ok = (now fs == t) &&
                    (isJust changed_val) &&
                    (changed_val /= stable_val)
           in if ok
              then Succeed
              else Fail msg

check_stable :: Code -> FileNum -> Integer -> String -> Checker
check_stable code fnum t msg =
    \cs -> let fs = getFS fnum cs
               stable_val = M.lookup code (stable fs)
               changed_val = M.lookup code (changing fs)
               ok = (now fs == t) &&
                    ((isNothing changed_val) || (changed_val == stable_val))
           in if ok
              then Succeed
              else Fail msg

check_X :: Code -> FileNum -> Integer -> String -> Checker
check_X code fnum t msg =
    \cs -> let fs = getFS fnum cs
               stable_val = M.lookup code (stable fs)
               changed_val = M.lookup code (changing fs)
               stable_ok = maybe False vcd_is_x stable_val
               no_change = isNothing changed_val
               change_ok = maybe False vcd_is_x changed_val
               ok = if (now fs < t)
                    then stable_ok
                    else (stable_ok && no_change) || change_ok
           in if ok
              then Succeed
              else Fail msg

check_Z :: Code -> FileNum -> Integer -> String -> Checker
check_Z code fnum t msg =
    \cs -> let fs = getFS fnum cs
               stable_val = M.lookup code (stable fs)
               changed_val = M.lookup code (changing fs)
               stable_ok = maybe False vcd_is_z stable_val
               no_change = isNothing changed_val
               change_ok = maybe False vcd_is_z changed_val
               ok = if (now fs < t)
                    then stable_ok
                    else (stable_ok && no_change) || change_ok
           in if ok
              then Succeed
              else Fail msg

setup_crc :: Code -> FileNum -> SeqCmd -> Checker
setup_crc code fnum seqcmd =
    \cs -> UpdateCS code fnum seqcmd success

check_crc :: Code -> FileNum -> Checker
check_crc code fnum =
    \cs -> let err = error $ "Could not find " ++ show code ++ " in checker state"
               cmd = M.findWithDefault err (fnum,code) (user cs)
               fs = getFS fnum cs
               changed_val =fromMaybe (0-1) $ (M.lookup code (changing fs)) >>= vcd_to_integer
               stable_val = fromMaybe (0-1) $ M.lookup code (stable fs) >>= vcd_to_integer
               time = now fs
               --
               timeok = timeOK (sc_nextTime cmd) time
               valueok = changed_val == (sc_crcfunction cmd) stable_val
               vnow = to_VCDValue (sc_width cmd) changed_val
               vexpected = to_VCDValue (sc_width cmd) $ (sc_crcfunction cmd) stable_val
               --
               doWaiting =
                   let prop = show cmd ++ " Started"
                       ok =  (sc_startVal cmd) == changed_val
                       cmd' = cmd {sc_state = Running
                                          ,sc_nextTime = incrTime time (sc_timeIncr cmd) }
                   in if (ok)
                      then SetProperty prop (\cs -> UpdateCS code fnum cmd' success)
                      else Succeed
               --
               doRunning =
                   let prop = show cmd ++ " Completed"
                       completed =  (sc_count cmd) == 1 + (sc_currentCount cmd)
                       cmd' = cmd {sc_currentCount = 1+ (sc_currentCount cmd)
                                  ,sc_nextTime = incrTime time (sc_timeIncr cmd)
                                  ,sc_state = if (completed) then Finished else Running}
                       errMsg = "at time: " ++ show time
                                ++ "\n  Expected: " ++ show vexpected
                                ++ "\n  Got:      " ++ show vnow
                                ++ "\n  " ++ show cmd
                   --
                   in case (completed, timeok, valueok) of
                        (True,  True, True)   -> UpdateCS code fnum cmd' (set_prop prop)
                        (False, True, True)   -> UpdateCS code fnum cmd' success
                        (_,     True, False)  -> UpdateCS code fnum cmd' $ failure $ "Incorrect Value: " ++ errMsg
                        (_,     False, True)  -> UpdateCS code fnum cmd' $ failure $ "Incorrect Time: " ++ errMsg
                        (_,     False, False) -> UpdateCS code fnum cmd' $ failure $ "Incorrect Time and Value: " ++ errMsg
               --
               doFinished = Fail $ "Signal " ++ sc_signal cmd ++ " changed at " ++ (show time)
                                    ++ " after completion. " ++ show cmd
           in case (sc_state cmd) of
                Waiting -> doWaiting
                Running -> doRunning
                Finished -> doFinished

-- This crc function is derivied from an BSV function in
-- testsuite/bsc.bluetcl/verific/probeinsetion/perftest/Flooder.bsv nextData
crcFunction :: (Integral a) => a -> Integer -> Integer
crcFunction width din = dout `rem` (1 `shiftL` w)
    where w = fromIntegral width
          dout = (din `xor` sh) + 1
          sh = (din `shiftL` 5) .|. (din `shiftR` (w-5))



-- Compiles CheckCmds into a CheckerState containing all of
-- the desired checkers.
initState :: [CheckCmd] -> Maybe FilePath -> Maybe FilePath -> CheckerState
initState cmds mfile1 mfile2 =
    let checkers = concatMap cmdToCheckers cmds
        initFS nm = FS { name     = fromMaybe "" nm
                       , scope    = []
                       , stable   = M.empty
                       , changing = M.empty
                       , ondefs   = M.empty
                       , enddefs  = []
                       , watching = M.empty
                       , endvcd   = []
                       , now      = 0
                       }
        cs = CS { props    = S.empty
                , waiting  = M.empty
                , user     = M.empty
                , state1   = initFS mfile1
                , state2   = initFS mfile2
                }
        (init_cs,msgs) = foldl execChecker (cs,[]) checkers
    in if (null msgs)
       then init_cs
       else internalError $ "Failures when initializing checkers:\n" ++ (unlines msgs)

-- Execute a checker and update the CheckerState and Fail messages
execChecker :: (CheckerState,[String]) -> Checker -> (CheckerState,[String])
execChecker (cs,msgs) chk =
    case (chk cs) of
      Succeed                -> (cs,msgs)
      (Fail msg)             -> (cs,msgs ++ [msg])
      (SetProperty prop nxt) ->
          let props' = S.insert prop (props cs)
          in execChecker (cs { props = props' },msgs) nxt
      (OnDef fnum name nxt_fn)  ->
          let fs = getFS fnum cs
              ondefs' = M.insertWith (++) name [nxt_fn] (ondefs fs)
          in (setFS fnum (fs { ondefs = ondefs' }) cs,msgs)
      (EndDef fnum nxt)      ->
          let fs = getFS fnum cs
              enddefs' = nxt:(enddefs fs)
          in (setFS fnum (fs { enddefs = enddefs' }) cs,msgs)
      (Wait t nxt)           ->
          let waiting' = M.insertWith (++) t [nxt] (waiting cs)
          in (cs { waiting = waiting' },msgs)
      (Watch fnum code nxt)  ->
          let fs = getFS fnum cs
              watching' = M.insertWith (++) code [nxt] (watching fs)
          in (setFS fnum (fs { watching = watching' }) cs,msgs)
      (EndVCD fnum nxt)      ->
          let fs = getFS fnum cs
              endvcd' = nxt:(endvcd fs)
          in (setFS fnum (fs { endvcd = endvcd' }) cs,msgs)
      (UpdateCS code fnum scmd nxt)  ->
          let user' = M.insert (fnum,code) scmd (user cs)
          in  execChecker  (cs {user=user'}, msgs) nxt


-- Process a VCD command and update the checker state
handleCmd :: (CheckerState,[String]) -> (FileNum,VCDCmd) -> (CheckerState,[String])
handleCmd (cs,msgs) (fnum, (Scope _ s)) =
    let fs = getFS fnum cs
        fs' = fs { scope = s:(scope fs) }
    in (setFS fnum fs' cs,msgs)
handleCmd (cs,msgs) (fnum, UpScope) =
    let fs = getFS fnum cs
        fs' = fs { scope = tail (scope fs) }
    in (setFS fnum fs' cs,msgs)
handleCmd (cs,msgs) (fnum, (Var _ width code s)) =
    let fs = getFS fnum cs
        stripped = takeWhile (/='[') s
        varname = intercalate "." $ reverse (stripped:(scope fs))
        activated = M.findWithDefault [] varname (ondefs fs)
        cs' = setFS fnum (fs { ondefs = (M.delete varname (ondefs fs)) }) cs
    in foldl execChecker (cs',msgs) (concatMap (\f -> f (code,width)) activated)
handleCmd (cs,msgs) (fnum, EndDefs) =
    let fs = getFS fnum cs
        activated = enddefs fs
        cs' = setFS fnum (fs { ondefs = M.empty, enddefs = [] }) cs
    in foldl execChecker (cs',msgs) activated
handleCmd (cs,msgs) (fnum, (Timestamp t)) =
    let (cs',msgs') = flushWaiting (cs,msgs) t
        fs = getFS fnum cs'
        stable' = M.union (changing fs) (stable fs)
        fs' = if (stable' == stable') -- force thunks
              then fs { stable = stable', changing = M.empty, now = t }
              else error "not good"
        cs_new_time = setFS fnum fs' cs'
    in (cs_new_time,msgs')
handleCmd (cs,msgs) (fnum, (Task "dumpvars" chs)) = foldl handleCmd (cs,msgs) (zip (repeat fnum) (map Change chs))
handleCmd (cs,msgs) (fnum, (Task _ _)) = (cs,msgs)
handleCmd (cs,msgs) (fnum, (Change chg)) =
    let fs        = getFS fnum cs
        code      = signal_code chg
        value     = new_value chg
        activated = M.findWithDefault [] code (watching fs)
        changing' = M.insert code value (changing fs)
        cs' = if (changing' == changing') -- force thunks
              then setFS fnum (fs { changing = changing' }) cs
              else error "not good"
    in foldl execChecker (cs',msgs) activated
handleCmd (cs,msgs) (fnum,(VCDErr msg text)) =
    let fs = getFS fnum cs
    in (cs, msgs ++ [(name fs) ++ ": " ++ msg ++ " in `" ++ text ++ "'"])
handleCmd (cs,msgs) _ = (cs,msgs)

-- Flush commands waiting at a particular time
flushWaiting :: (CheckerState,[String]) -> Integer -> (CheckerState,[String])
flushWaiting (cs,msgs) t =
    let (before,at,later) = M.splitLookup t (waiting cs)
        cs' = cs { waiting = case (at) of
                               (Just chks) -> M.insert t chks later
                               Nothing     -> later
                 }
        activated = concat (M.elems before)
    in foldl execChecker (cs',msgs) activated

-- A left fold for commands which exits early once all non-end checkers
-- have been dispatched
foldCmds :: ((CheckerState,[String]) -> (FileNum,VCDCmd) -> (CheckerState,[String]))
         -> (CheckerState,[String]) -> [(FileNum,VCDCmd)] -> (CheckerState,[String])
foldCmds handler state [] = state
foldCmds handler state@(cs,msgs) (cmd:rest) =
  let fs1 = getFS 1 cs
      fs2 = getFS 2 cs
      quiescent1 = M.null (waiting cs) &&
                   M.null (ondefs fs1) &&
                   null (enddefs fs1) &&
                   M.null (watching fs1)
      quiescent2 = M.null (waiting cs) &&
                   M.null (ondefs fs2) &&
                   null (enddefs fs2) &&
                   M.null (watching fs2)
  in if (quiescent1 && quiescent2)
     then state
     else foldCmds handler (handler state cmd) rest

-- -------------------------------------------------------------------
-- Run the checkers over a single file's command stream, returning
-- the failure messages (empty on success)

checkStream :: [CheckCmd] -> FilePath -> VCD -> [String]
checkStream cmds fname stream =
    let tagged      = map (\x -> (file1,x)) stream
        cs0         = initState cmds (Just fname) Nothing
        (cs1,msgs1) = foldCmds handleCmd (cs0,[]) tagged
        (cs2,msgs2) = flushWaiting (cs1,msgs1) (now (state1 cs1) + 1)
        (cs3,msgs3) = foldl execChecker (cs2,msgs2) (endvcd (state1 cs2))
        stranded    = waiting cs3
        smsgs       = if (M.null stranded)
                      then []
                      else [ intercalate "\n" $ [ fname ++ " ends before checkers at time: " ] ++
                                                 [ "  " ++ (show t) | t <- M.keys stranded ]
                           ]
    in msgs3 ++ smsgs
