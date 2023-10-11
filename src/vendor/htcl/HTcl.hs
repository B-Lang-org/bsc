{-# LANGUAGE CPP, ForeignFunctionInterface, CApiFFI #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -fno-warn-unused-matches -Werror #-}

-- User level Haskell interface for TCL
-- Users of this module should not need to understand the tcl
-- implementation underneath this module
--
-- Ed Czeck, Bluespec Inc
-- April 2007


{-
  TODO
   - I do not like the error handling, via the Maybe type, but some may not want to throw errors
   - options processing (getOptions :: TclInterp -> [TclObj] -> [OptionDesc a] -> IO (a, [TclObj])
   - add import for Tcl_Eval
-}

module HTcl
    (
     -- Status return values, and an enum
     htcl_OK
    ,htcl_Error
    ,TclStatus

    ,TclObjCvt(..)
    ,TclInterp
    ,TclObj
    -----------------------
    -- Registering command and other command
    --  Types for command objects
    ,TclObjCmdProc
    ,TclCmdDeleteProc
    ,TclClientData
    ,htclRawFnToTclCmd
    ,htclFnToTclCmd
    ,htclCheckCmd
    ,htclMakeCmdDesc
    ,HTclCmdDesc(..)
    ,HTclCmdElem(..)
    ,HTclArgType(..)
    ,HTclCmdGrammar(..)
    ,HTclCmdFn
    ,HTclCheckedCmdFn
    ,htclRegisterCommand
    ,htclRegisterCommandFull
    ,htclRegCommands
    ,htclCmdName
    ,htclFirstCmdElem
    ,htclDescribeCmdGrammar
    ,htclGrammarShortDesc
    ,htclMatchGrammar
    ,htclCanMatchNull
    ,htclSetReturnVal           -- may not be needed
    -- Dealing with Errors
    ,htcl_AddObjErrorInfo
    ,htclErrorCatcher
    -------------------------------
    -- Converting from Obj to Native Haskell types
    ,htclArgsToTcl
    -- primitives
    ,htclObjToInt
    ,htclObjToBool
    ,htclObjToDouble
    ,htclObjToString
    ,htclObjToList
    -- composite
    ,htclObjToListInt
    ,htclObjToListDouble
    ,htclObjToListString
    -------------------------------
    ,HTclObj(..)
    -- Conversion to from objects to fields of this type
    ,HTclObjCvt(..)
    ,tag
    ,tagStr
    ,tagInt
    ,tagLst
    ,tagManyStr
    ,tagManyInt
    ,joinHTObj
    ,joinHTObjs
    -----------------
    -- Grammar combinators
    , kw
    , tclcmd
    , arg
    , (.+.)
    , oneOf
    , optional
    , atLeast
    -----------------
    -- Tests and Experiments
    )
where

import Prelude

import Data.Word

import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Marshal.Utils
import Foreign.Ptr
import Foreign.C.Types
import Foreign.C.String
import Data.Time.Clock
import Data.Time.Clock.POSIX

import Foreign.ForeignPtr
import Foreign.ForeignPtr.Unsafe(unsafeForeignPtrToPtr)

import Control.Monad(foldM, mplus, msum, when)
import System.IO.Error
import System.Exit(ExitCode(..))
import Data.List(intersperse, nub, isPrefixOf)

import qualified Control.Exception as CE

--import Debug.Trace
traceCalls :: Bool
traceCalls = False


-- cast function
castE :: (Enum a, Enum b) => a -> b
castE = toEnum . fromEnum

castI :: (Integral a, Integral b) => a -> b
castI = fromIntegral

castD :: (RealFloat a, RealFloat b) => a -> b
castD = (uncurry encodeFloat) . decodeFloat

--------------------------------------------------------------------------------
-- Common TCL function status
-- Note break, continue are not (yet) defined


data TclStatus = TCL_OK | TCL_ERROR | TCL_RETURN | TCL_BREAK | TCL_CONTINUE
                 deriving (Eq)

instance Enum TclStatus where
    -- toEnum :: Int -> a
    toEnum 0 = TCL_OK
    toEnum 1 = TCL_ERROR
    toEnum 2 = TCL_RETURN
    toEnum 3 = TCL_BREAK
    toEnum 4 = TCL_CONTINUE
    toEnum x = error ("Unexpected Tcl status value: " ++ show x)
    -- fromEnum :: a -> Int
    fromEnum TCL_OK       = 0
    fromEnum TCL_ERROR    = 1
    fromEnum TCL_RETURN   = 2
    fromEnum TCL_BREAK    = 3
    fromEnum TCL_CONTINUE = 4

-- Get real values from tcl world -- there should be an easier way to do this for #defines!
foreign import capi "tcl.h value TCL_OK"
 htcl_OKc :: CInt
foreign import capi "tcl.h value TCL_ERROR"
 htcl_Errorc :: CInt


-- exported versions of tcl status using native haskell types
htcl_OK :: TclStatus
htcl_OK = TCL_OK

htcl_Error :: TclStatus
htcl_Error = TCL_ERROR


--------------------------------------------------------------------------------

-- The interperter -- no need for a finalizer call here
data XTclInterp = XTclInterp
type TclInterp = Ptr XTclInterp

-- Client data structure
type TclClientData = Ptr Int


-- Types and functions to deal with     Tcl Objects
-- Wrapper for foreign (tcl objects)
-- Objects which are passed to and from commands
data {-# CTYPE "Tcl_Obj" #-} XTclObj = XTclObj
type PTclObj = Ptr XTclObj
type TclObj = ForeignPtr XTclObj
type PTclObjArray = Ptr PTclObj


-- Foreign import functions --     Objects
foreign import ccall "Tcl_NewIntObj"
 tcl_NewIntObj :: CInt -> IO (PTclObj)

foreign import ccall "Tcl_NewWideIntObj"
 tcl_NewWideIntObj :: CLLong -> IO (PTclObj) -- tcl uses long long

foreign import ccall "Tcl_NewDoubleObj"
 tcl_NewDoubleObj :: CDouble -> IO PTclObj -- tcl double

foreign import ccall "Tcl_NewStringObj"
 tcl_NewStringObj :: Ptr CChar -> CInt -> IO PTclObj

foreign import ccall "Tcl_NewListObj"
 tcl_NewListObj :: CInt -> Ptr PTclObj ->  IO PTclObj


---------------------------------------------------------------
-- Reference count on Objects
foreign import capi "tcl.h Tcl_DecrRefCount"
 tcl_DecrRefCount :: PTclObj -> IO ()

foreign import capi "tcl.h Tcl_IncrRefCount"
 tcl_IncrRefCount :: PTclObj -> IO ()

foreign import ccall "&htcl_finalizeTclObj"
  tcl_finalizeTclObj :: FunPtr (PTclObj -> IO ())

tclObjFinalizer :: FinalizerPtr XTclObj
tclObjFinalizer = tcl_finalizeTclObj

-- Function to wrap tcl object into finalizer
wrapPtrForExport :: PTclObj -> IO TclObj
wrapPtrForExport pobj = do
  tcl_IncrRefCount pobj
  fp <- newForeignPtr_  pobj
  addForeignPtrFinalizer tclObjFinalizer fp
  return fp

---------------------------------------------------------
-- A class to provide means to convert to tcl objects and
-- haskell objects
-- 2 members are defined, one to convert to Ptr XTclObj and the other to convert to
-- ForeignPtr XTclObj.  Only the later should be used externally
class TclObjCvt a  where
    toTclObj    :: a -> IO TclObj


-- an instance of TclObjCvt call for Unit
instance  TclObjCvt () where
    toTclObj i  = toTclObj ""

-- an instance of TclObjCvt call for Bool
instance  TclObjCvt Bool where
    toTclObj b  = tcl_NewIntObj (if b then 1 else 0) >>= wrapPtrForExport

-- an instance of TclObjCvt call for Int
instance  TclObjCvt Int where
    toTclObj i  = tcl_NewIntObj (castI i) >>= wrapPtrForExport

-- an instance of TclObjCvt call for Integer
-- use show since value can be greater than native representation
instance  TclObjCvt Integer where
    toTclObj i  = toTclObj (show i)

-- an instance of TclObjCvt call for Word32
instance  TclObjCvt Word32 where
    toTclObj i  = tcl_NewIntObj (castI i) >>= wrapPtrForExport

-- an instance of TclObjCvt call for Word64
instance  TclObjCvt Word64 where
    toTclObj i  = tcl_NewWideIntObj (castI i) >>= wrapPtrForExport

-- instance for Double
instance TclObjCvt Double where
    toTclObj d = tcl_NewDoubleObj (castD d) >>= wrapPtrForExport

-- instance for String
instance {-# OVERLAPPING #-} TclObjCvt String where
    -- XXX ?? toTclObj "" = withCStringLen "{}" (\(cs,l) -> tcl_NewStringObj cs l) >>= wrapPtrForExport
    toTclObj s = do
      withCStringLen s (\(cs,l) -> tcl_NewStringObj cs (castI l)) >>= wrapPtrForExport

-- instance for UTCTime
instance TclObjCvt UTCTime where
    toTclObj t = toTclObj ((round (utcTimeToPOSIXSeconds t)) :: Integer)

-- instance for TclObj
instance TclObjCvt TclObj where
    toTclObj i  = return i

instance TclObjCvt PTclObj where
    toTclObj i  = wrapPtrForExport i

-- instance for List
instance {-# OVERLAPPABLE #-} TclObjCvt a =>  TclObjCvt [a] where
    toTclObj os = do
      let len = length os
      fpobjs <- mapM toTclObj os
      let pobjs = map unsafeForeignPtrToPtr fpobjs
      outs <- newArray pobjs
      res <- tcl_NewListObj (castI len) outs
      free outs
      mapM_ touchForeignPtr fpobjs
      wrapPtrForExport res

instance TclObjCvt a => TclObjCvt (Maybe a)  where
    toTclObj (Just x) = toTclObj x >>= (\p -> toTclObj (TLst [TStr "Just", TCL p]))
    toTclObj (Nothing) = toTclObj (TLst [TStr "Nothing"])

instance (TclObjCvt a, TclObjCvt b) => TclObjCvt (a,b)  where
    toTclObj (x,y) = do
      ox <- toTclObj x
      oy <- toTclObj y
      toTclObj [ox,oy]

instance (TclObjCvt a, TclObjCvt b, TclObjCvt c) => TclObjCvt (a,b,c)  where
    toTclObj (x,y,z) = do
      ox <- toTclObj x
      oy <- toTclObj y
      oz <- toTclObj z
      toTclObj [ox,oy,oz]

instance (TclObjCvt a, TclObjCvt b, TclObjCvt c, TclObjCvt d) =>
         TclObjCvt (a,b,c,d)  where
    toTclObj (w,x,y,z) = do
      ow <- toTclObj w
      ox <- toTclObj x
      oy <- toTclObj y
      oz <- toTclObj z
      toTclObj [ow,ox,oy,oz]

instance (TclObjCvt a, TclObjCvt b, TclObjCvt c, TclObjCvt d, TclObjCvt e) =>
         TclObjCvt (a,b,c,d,e)  where
    toTclObj (v,w,x,y,z) = do
      ov <- toTclObj v
      ow <- toTclObj w
      ox <- toTclObj x
      oy <- toTclObj y
      oz <- toTclObj z
      toTclObj [ov,ow,ox,oy,oz]

-- Yes, this gets used (shamefully)
instance (TclObjCvt a, TclObjCvt b, TclObjCvt c, TclObjCvt d, TclObjCvt e
         ,TclObjCvt f, TclObjCvt g, TclObjCvt h, TclObjCvt i, TclObjCvt j
         ) => TclObjCvt (a,b,c,d,e,f,g,h,i,j)  where
    toTclObj (q,r,s,t,u,v,w,x,y,z) = do
      oq <- toTclObj q
      or' <- toTclObj r
      os <- toTclObj s
      ot <- toTclObj t
      ou <- toTclObj u
      ov <- toTclObj v
      ow <- toTclObj w
      ox <- toTclObj x
      oy <- toTclObj y
      oz <- toTclObj z
      toTclObj [oq,or',os,ot,ou,ov,ow,ox,oy,oz]

-- Conversion of a pointer to a TCL representation
instance TclObjCvt WordPtr where
    toTclObj p = toTclObj (show p)

---------------------------------------------------------------
-- Conversion from Objects to Native types
foreign import ccall "Tcl_GetIntFromObj"
  tcl_GetIntFromObj :: TclInterp -> PTclObj -> Ptr CInt -> IO CInt

foreign import ccall "Tcl_GetLongFromObj"
  tcl_GetLongFromObj :: TclInterp -> PTclObj -> Ptr CLong -> IO CLong

foreign import ccall "Tcl_GetBooleanFromObj"
  tcl_GetBooleanFromObj :: TclInterp -> PTclObj -> Ptr CInt -> IO CInt

foreign import ccall "Tcl_GetDoubleFromObj"
  tcl_GetDoubleFromObj :: TclInterp -> PTclObj -> Ptr CDouble -> IO CInt

foreign import ccall "Tcl_GetStringFromObj"
  tcl_GetStringFromObj :: PTclObj -> Ptr CInt -> IO (Ptr CChar)  -- TCL

foreign import ccall "Tcl_ListObjGetElements"
 tcl_ListObjGetElements :: TclInterp -> PTclObj -> Ptr CInt -> Ptr PTclObjArray -> IO CInt

--------------------------------------------------------------------------------
-- TODO Never got this to work quite right
foreign import ccall "Tcl_AppendAllObjTypes"
 tcl_AppendAllObjTypes :: TclInterp -> PTclObj -> IO ()


--------------------------------------------------------------------------------
-- Types and functions to deal with command objects and registering call backs
-- Tcl command block
data XTclCommand =  XTclCommand
type TclCommand  = Ptr XTclCommand

-- Types for Pointers to functions for added tcl command objects
type TclObjCmdProc  = TclClientData -> TclInterp -> Int -> PTclObjArray -> IO Int
type PTclObjCmdProc = FunPtr TclObjCmdProc

-- Types for Pointer to delete function
type TclCmdDeleteProc  = TclClientData -> IO ()
type PTclCmdDeleteProc = FunPtr TclCmdDeleteProc

-- Foreign import function --     Command objects
foreign import ccall "Tcl_CreateObjCommand"
 tcl_CreateObjCommand :: TclInterp -> CString -> PTclObjCmdProc -> TclClientData -> PTclCmdDeleteProc -> IO TclCommand

--  wrappers to convert Haskell commands to pointer to C functions
foreign import ccall "wrapper"
 wrapHTclCommand :: TclObjCmdProc -> IO PTclObjCmdProc
foreign import ccall "wrapper"
 wrapHTclDeleteCommand :: TclCmdDeleteProc -> IO PTclCmdDeleteProc

-- Functions to deal with command registrations
htclRegisterCommandFull :: TclInterp  -> String -> TclObjCmdProc -> TclClientData -> Maybe TclCmdDeleteProc -> IO TclCommand
htclRegisterCommandFull interp cmdname hcmd cd hdelfun = do
  cmd <- wrapHTclCommand hcmd
  dcmd <- case hdelfun of
            Nothing -> return nullFunPtr
            Just df -> wrapHTclDeleteCommand df
  withCString cmdname (\s -> tcl_CreateObjCommand interp s cmd cd dcmd)

htclRegisterCommand :: (TclObjCvt a) =>
                       TclInterp -> String -> HTclCmdGrammar ->
                       (HTclCmdFn a) -> IO TclCommand
htclRegisterCommand interp cmdname grmr hcmd = do
  let hcmd' = htclFnToTclCmd grmr hcmd
  htclRegisterCommandFull interp cmdname hcmd' nullPtr Nothing

------------------------------------------------------------------------------
-- Exception catching functions

htclErrorCatcher :: TclInterp -> CE.SomeException -> IO Int
htclErrorCatcher interp e =
    do let errString = msum [ handleIOException e, handleErrorCall e, handleExit e]
       case errString of
         (Just s) -> tclSetAndAddErrorInfo interp s
         Nothing  -> tclSetAndAddErrorInfo interp ("Error: exception caught: " ++ show e)
  where -- these are in the Maybe monad
        handleIOException ex =
            do err <- (CE.fromException ex)::(Maybe CE.IOException)
               let msg = ioeGetErrorString err
               return $ if (isUserError err)
                        then "Error: " ++ msg
                        else msg
        handleErrorCall ex =
            do (CE.ErrorCall msg) <- (CE.fromException ex)::(Maybe CE.ErrorCall)
               return $ if (("Error" `isPrefixOf` msg) || ("error" `isPrefixOf` msg))
                        then msg
                        else "Error: exception caught: " ++ msg
        handleExit ex =
            do exitcode <- (CE.fromException ex)::(Maybe ExitCode)
               return $ "Error: exception caught. See stderr for more details; code is: " ++ (show exitcode)

tclSetAndAddErrorInfo :: TclInterp -> String -> IO (Int)
tclSetAndAddErrorInfo interp s | s == "" = do
  return 1
tclSetAndAddErrorInfo interp s | s == "Error: " = do
  return 1
tclSetAndAddErrorInfo interp s = do
    _ <- htcl_AddObjErrorInfo interp s
    htclSetReturnVal interp s
    return 1

------------------------------------------------------------------
-- Turning Haskell functions and associated command grammar
-- descriptions into TCL command procedures.

-- This is the type of Haskell function which is used to implement
-- a TCL command.  The Haskell function takes a list of strings
-- (the arguments to the command) and executes in the IO monad.
-- Before it can be registered, it should be wrapped in a grammar
-- checker to create a HTclCheckedCmdFn.
type HTclCmdFn a = [String] -> IO a

-- This is the type of Haskell function which implements a TCL
-- command with an integrated grammar check (see htclCheckCmd).
type HTclCheckedCmdFn a = TclInterp -> [TclObj] -> IO a

-- The list of strings passed as arguments to a command can be
-- constrained by a grammar describing the format of the command.

-- Types of arguments allowed in a command grammar
data HTclArgType = StringArg | IntArg | PtrArg | DoubleArg | BoolArg
  deriving (Eq,Show)

-- A grammar describes allowed sequences of keywords and arguments
data HTclCmdElem = Keyword { literal      :: String
                           , kw_desc      :: String
                           , kw_long_desc :: String
                           }
                 | Argument { arg_name :: String
                            , arg_type :: HTclArgType
                            , arg_desc :: String
                            }
                 | Command { literal       :: String
                           , cmd_desc      :: String
                           , cmd_long_desc :: String
                           , cmd_namespace :: String
                           }
  deriving (Eq,Show)

-- A command grammar follows standard practice for sequencing,
-- alternatives and repetition
data HTclCmdGrammar = Exactly HTclCmdElem
                    | Sequence HTclCmdGrammar HTclCmdGrammar
                    | ChooseFrom [HTclCmdGrammar]
                    | ZeroOrMore HTclCmdGrammar
                    | OneOrMore HTclCmdGrammar
                    | None
  deriving (Eq,Show)

-- combinators for more succinct grammar expressions

kw :: String -> String -> String -> HTclCmdGrammar
kw s sd ld = Exactly (Keyword s sd ld)

tclcmd :: String -> String -> String -> String -> HTclCmdGrammar
tclcmd s ns sd ld = Exactly (Command s sd ld ns)

arg :: String -> HTclArgType -> String -> HTclCmdGrammar
arg n t d = Exactly (Argument n t d)

(.+.) :: HTclCmdGrammar -> HTclCmdGrammar -> HTclCmdGrammar
(.+.) = Sequence

oneOf :: [HTclCmdGrammar] -> HTclCmdGrammar
oneOf gs = ChooseFrom (nub $ concatMap asList gs)
    where asList (ChooseFrom xs) = xs
          asList x               = [x]

optional :: HTclCmdGrammar -> HTclCmdGrammar
optional (ChooseFrom gs) = oneOf $ (filter (/=None) gs) ++ [None]
optional g = oneOf [g,None]

atLeast :: Int -> HTclCmdGrammar -> HTclCmdGrammar
atLeast 0 g = ZeroOrMore g
atLeast 1 g = OneOrMore g
atLeast n g = g .+. (atLeast (n-1) g)

-- Get a string describing a command element
cmdElemString :: HTclCmdElem -> String
cmdElemString (Keyword s _ _) = s
cmdElemString (Command s _ _ ns) = s
cmdElemString (Argument s _ _) = "<" ++ s ++ ">"

-- Find the first element admitted by a grammar.  For a normal command,
-- this will be a unique keyword.
htclFirstCmdElem :: HTclCmdGrammar -> Maybe HTclCmdElem
htclFirstCmdElem (Exactly e)      = Just e
htclFirstCmdElem (Sequence g1 g2) = (htclFirstCmdElem g1) `mplus` (htclFirstCmdElem g2)
htclFirstCmdElem (ChooseFrom gs)  = msum (map htclFirstCmdElem gs)
htclFirstCmdElem (ZeroOrMore g)   = htclFirstCmdElem g
htclFirstCmdElem (OneOrMore g)    = htclFirstCmdElem g
htclFirstCmdElem None             = Nothing

-- Describe a command grammar in standard notation
htclDescribeCmdGrammar :: HTclCmdGrammar -> Int -> String
htclDescribeCmdGrammar grm limit = let (desc,_,_) = prt 2 limit grm in desc
  where prt :: Int -> Int -> HTclCmdGrammar -> (String,Int,Bool)
        prt _ lmax (Exactly e) =
            let s = cmdElemString e
                len = length s
            in if (len > lmax) then ("...",3,True) else (s,len,False)
        prt n lmax (Sequence g1 g2) =
            let (s1,l1,a1) = prt 2 lmax g1
                body = if a1
                       then (s1,l1,a1)
                       else let (s2,l2,a2) = (prt 2 (lmax-l1-1) g2)
                            in (s1 ++ " " ++ s2, l1 + 1 + l2, a2)
            in paren_if (n > 2) body
        prt n lmax (ChooseFrom gs) =
            let gs' = filter (/= None) gs
                is_optional = None `elem` gs
                num_seps = (length gs')-1
                sub_lmax = lmax - (3*num_seps) - (length gs')
                (strs,lens,abbrevs) = unzip3 $ map (prt 1 sub_lmax) gs'
                body = concat (intersperse " | " strs)
                body_len = (sum lens) + (3 * num_seps)
                body_abbrev = or abbrevs
                (res,len,abbrev) =
                    if is_optional
                    then ("[" ++ body ++ "]", body_len + 2, body_abbrev)
                    else paren_if (n > 1) (body,body_len,body_abbrev)
            in if ((len > lmax) || body_abbrev)
               then if (lmax < 17)
                    then ("...",3,True)
                    else ("...subcommands...",17,True)
               else (res,len,False)
        prt n lmax (ZeroOrMore g) =
            let (res,len,ab) = prt 3 lmax g
            in (res ++ "*", len+1, ab)
        prt n lmax (OneOrMore g) =
            let (res,len, ab) = prt 3 lmax g
            in (res ++ "+", len+1, ab)
        prt _ _ None = ("",0,False)
        paren_if :: Bool -> (String,Int,Bool) -> (String,Int,Bool)
        paren_if True  (x,n,a) = ("(" ++ x ++ ")", n+2, a)
        paren_if False (x,n,a) = (x,n,a)

-- Given a TCL object and an argument type, returns Nothing if the
-- string does not represent a value of the given type.  If the
-- string does represent a value of the given type, returns Just
-- of another string which is guaranteed to be parsable by the
-- Haskell read function into a value of the given type.
matchArgType :: TclInterp -> TclObj -> HTclArgType -> IO (Maybe String)
matchArgType i o StringArg = htclObjToMString i o
matchArgType i o IntArg    = do mi <- htclObjToMInt i o
                                return $ mi >>= (Just . show)
matchArgType i o PtrArg    = do mi <- htclObjToMWordPtr i o
                                return $ mi >>= (Just . show)
matchArgType i o DoubleArg = do md <- htclObjToMDouble i o
                                return $ md >>= (Just . show)
matchArgType i o BoolArg   = do mb <- htclObjToMBool i o
                                return $ mb >>= (Just . show)

-- Match a list of TCl objects representing a command against its grammar.
-- The result is a tuple containing:
--   1. A list of (String,HTclCmdElem) pairs which shows which
--      part of the grammar matched each part of the input string.
--      The list is in reverse order of the argument string.
--   2. A list of inputs objects which were not matched.
--   3. A remaining portion of the grammar which was not matched.
-- So a result matching (_,[],_) indicates that all of the input
-- was successfully consumed.  A result matching (_,_,None) means
-- that the the input string matched the entire grammar. So:
--   (_, [], None)        => match of complete grammar with no additional input
--   (_, rest, None)      => match of complete grammar but with extra input
--   (_, [], remaining)   => match of a prefix of the grammar
--   (_, rest, remaining) => mismatch between input and grammar
htclMatchGrammar :: TclInterp -> [TclObj] -> HTclCmdGrammar ->
                    IO ([(String,HTclCmdElem)], [TclObj], HTclCmdGrammar)
htclMatchGrammar interp objs cmd_grammar = worker ([], objs, cmd_grammar)
    where worker :: ([(String,HTclCmdElem)], [TclObj], HTclCmdGrammar) ->
                    IO ([(String,HTclCmdElem)], [TclObj], HTclCmdGrammar)
          worker (matched, ws, (Sequence None g2)) =
              worker (matched, ws, g2)
          worker (matched, [], g) =
              return (matched, [], g)
          worker (matched, ws, None) =
              return (matched, ws, None)
          worker x@(matched, (w:rest), (Exactly el@(Keyword s' _ _))) = do
              str <- htclObjToMString interp w
              case str of
                (Just s) -> if (s == s')
                            then return ((s,el):matched, rest, None)
                            else return x
                Nothing  -> return x
          worker x@(matched, (w:rest), (Exactly el@(Command s' _ _ _))) = do
              str <- htclObjToMString interp w
              case str of
                (Just s) -> return ((s,el):matched, rest, None)
                Nothing  -> return x
          worker x@(matched, (w:rest), (Exactly el@(Argument _ ty _))) = do
              str <- matchArgType interp w ty
              case str of
                (Just s) -> return ((s,el):matched, rest, None)
                Nothing  -> return x
          worker x@(matched, ws, (Sequence g1 g2)) = do
              (matched', ws', g1') <- worker (matched, ws, g1)
              if (ws == ws')
               then return x -- no parse on g1
               else worker (matched', ws', (Sequence g1' g2))
          worker x@(matched, ws, (ChooseFrom gs)) = do
              choices <- sequence [ worker (matched, ws, g) | g <- gs ]
              let good = [ (matched', ws', g')
                         | (matched', ws', g') <- choices
                         , ws /= ws'
                         ]
              case good of
               []     -> return x   -- no options matched
               (hd:_) -> return hd  -- choose the first match
          worker (matched, ws, (ZeroOrMore g)) = do
              (matched', ws', g') <- worker (matched, ws, g)
              if ((ws == ws') || (g' /= None))
               then return (matched, ws, None) -- did not match, but is OK
               else worker (matched', ws', (ZeroOrMore g))
          worker x@(matched, ws, (OneOrMore g)) = do
              (matched', ws', g') <- worker (matched, ws, g)
              if ((ws == ws') || (g' /= None))
               then return x -- did not match even once, so not OK
               else worker (matched', ws', (ZeroOrMore g))

-- Regular grammar matching gives the shortest match (it does not try
-- to extend a match of [] with grammars which admit None).
-- To determine if such a match also represents a match of the complete
-- grammar (because the remaining grammar admits []),  this function
-- is provided.
htclCanMatchNull :: HTclCmdGrammar -> Bool
htclCanMatchNull None = True
htclCanMatchNull (Exactly _) = False
htclCanMatchNull (Sequence g1 g2) = all htclCanMatchNull [g1,g2]
htclCanMatchNull (ChooseFrom gs) = any htclCanMatchNull gs
htclCanMatchNull (ZeroOrMore _) = True
htclCanMatchNull (OneOrMore g) = htclCanMatchNull g

-- Provide a short description for a command grammar
htclGrammarShortDesc :: HTclCmdGrammar -> String
htclGrammarShortDesc g = case (htclFirstCmdElem g) of
                           Just (Keyword _ s _)   -> s
                           Just (Command _ s _ _) -> s
                           Just (Argument _ _ s)  -> s
                           Nothing                -> ""

-- Add grammar checks to a Haskell function for a TCL command.
-- This wraps a Haskell function taking a list of strings to
-- one taking a TCL interpreter and list of TCL objects.  The
-- wrapper handles conversion of the TCL objects to Haskell
-- strings and checks the input against the grammar so that
-- underlying function only needs to deal with input which matches
-- the grammar.
htclCheckCmd :: HTclCmdGrammar -> (HTclCmdFn a) -> (HTclCheckedCmdFn a)
htclCheckCmd grm fn interp args = do
    res <- htclMatchGrammar interp args grm
    when (traceCalls) $
         do
           argStrs <- mapM (htclObjToMString interp)  args
           putStrLn $ "TCL: " ++ (unwords $ map (maybe "" id) argStrs)
    let call_fn matched =
          case map fst (reverse matched) of
            (_:tl) -> fn tl
            _ -> ioError $ userError "Internal Error: htclCheckCmd: missing command name"
    case res of
      (matched, [], None) -> call_fn matched
      (_, extra, None) -> do strs <- mapM (htclObjToString interp) extra
                             cmdExtraArgs strs
      (matched, [], g) -> if (htclCanMatchNull g)
                          then call_fn matched
                          else cmdTooShort g
      (_, ws, g) -> do strs <- mapM (htclObjToString interp) ws
                       cmdBadSyntax strs g


-- Convert a Haskell function including a grammar check into a
-- TCL object which can be registered as a command procedure.
htclRawFnToTclCmd :: (TclObjCvt a) => (HTclCheckedCmdFn a) -> TclObjCmdProc
htclRawFnToTclCmd f =
    (\cd interp objc objv ->
        CE.catch (do -- process command arguments
                     args <- htclArgsToTcl interp objc objv
                     -- execute command function
                     res <- f interp args
                     -- handle return value
                     htclSetReturnVal interp res
                     return 0
                 ) (htclErrorCatcher interp)
    )

-- Wrap a Haskell function with its grammar check and convert
-- it into a TCL object which can be registered as a command
-- procedure.
htclFnToTclCmd :: (TclObjCvt a) =>
                  HTclCmdGrammar -> (HTclCmdFn a) -> TclObjCmdProc
htclFnToTclCmd grmr f = htclRawFnToTclCmd (htclCheckCmd grmr f)

-- Structure to hold all information about a command
data HTclCmdDesc = HTclCmdDesc {grammar :: HTclCmdGrammar
                               ,cd_func    :: TclObjCmdProc
                               }

htclMakeCmdDesc :: (TclObjCvt a) =>
                   HTclCmdGrammar -> (HTclCmdFn a) -> HTclCmdDesc
htclMakeCmdDesc grmr f = HTclCmdDesc grmr (htclFnToTclCmd grmr f)

htclCmdName :: HTclCmdDesc -> String
htclCmdName cmd = case (htclFirstCmdElem (grammar cmd)) of
                    (Just e) -> cmdElemString e
                    Nothing  -> ""

htclCmdNameNamespace :: HTclCmdDesc -> String
htclCmdNameNamespace cmd = case (htclFirstCmdElem (grammar cmd)) of
                    (Just (Command s _ _ ns)) -> if null ns then s else (ns ++ "::" ++ s)
                    _ -> error "Tcl Command grammar did not begin with a Command."


-- Register commands with a TCL interpreter
-- False reports an error
htclRegCommands :: TclInterp -> [HTclCmdDesc] -> IO Bool
htclRegCommands interp cmds = do
  foldM reg1Cmd True cmds
    where reg1Cmd :: Bool -> HTclCmdDesc -> IO Bool
          reg1Cmd True cmd@(HTclCmdDesc{}) = do
            pc <- htclRegisterCommandFull interp (htclCmdNameNamespace cmd) (cd_func cmd) nullPtr Nothing
            return (pc /= nullPtr)
          reg1Cmd False _ = return False

--------------------------------------------------------------------------------
-- Returning values and errors via the interp
foreign import ccall "Tcl_SetObjResult"
  tcl_SetObjResult :: TclInterp -> PTclObj -> IO ()

foreign import ccall "Tcl_AddObjErrorInfo"
 tcl_AddObjErrorInfo :: TclInterp -> Ptr CChar -> CInt -> IO ()

-- Adds String to the global tcl variable errorInfo
htcl_AddObjErrorInfo :: TclInterp -> String -> IO TclStatus
htcl_AddObjErrorInfo interp s = do
  let str = case (s) of
              ""       -> ""
              "\n"     -> ""
              ('\n':r) -> r
              x        -> x
  withCStringLen str (\(pc,len) -> tcl_AddObjErrorInfo interp pc (castI len))
  return htcl_Error

-- Not used
foreign import ccall "Tcl_WrongNumArgs"
        htcl_WrongNumArgs :: TclInterp -> CInt -> PTclObjArray -> CChar -> IO ()

htclSetReturnVal :: ( TclObjCvt a) => TclInterp -> a -> IO ()
htclSetReturnVal interp hobj = do
  res <- toTclObj hobj
  withForeignPtr res (tcl_SetObjResult interp)


------------------------------------------------------------------------------------------
-- A Haskell Structure to represent a tcl structure
data HTclObj  = TLst [HTclObj]
              | TStr String
              | TInt Int
              | TDbl Double
              | TCL TclObj
 deriving (Show, Eq)

-- instance for HTclObj
instance  TclObjCvt HTclObj where
    toTclObj (TLst objs) = toTclObj objs
    toTclObj (TStr s)    = toTclObj s
    toTclObj (TInt i)    = toTclObj i
    toTclObj (TDbl d)    = toTclObj d
    toTclObj (TCL o)    = toTclObj o
    --

class HTclObjCvt a where
    toHTObj :: a -> HTclObj

instance HTclObjCvt () where
    toHTObj _ = TStr ""

instance HTclObjCvt HTclObj  where
    toHTObj = id

instance HTclObjCvt Int where
    toHTObj i = TInt i

instance HTclObjCvt Integer where
    toHTObj i = TStr $ show i

instance {-# OVERLAPPING #-} HTclObjCvt String where
    toHTObj s = TStr s

instance HTclObjCvt Double where
    toHTObj s = TDbl s

instance HTclObjCvt Bool where
    toHTObj True  = TStr "True"
    toHTObj False = TStr "False"

instance (HTclObjCvt a, HTclObjCvt b) => HTclObjCvt (a,b) where
    toHTObj (x,y) = TLst [toHTObj x, toHTObj y]

instance (HTclObjCvt a, HTclObjCvt b, HTclObjCvt c) => HTclObjCvt (a,b,c) where
    toHTObj (x,y,z) = TLst [toHTObj x, toHTObj y, toHTObj z]

instance (HTclObjCvt a , HTclObjCvt b, HTclObjCvt c, HTclObjCvt d) => HTclObjCvt (a,b,c,d) where
    toHTObj (x,y,z,w) = TLst [toHTObj x, toHTObj y, toHTObj z, toHTObj w]

instance {-# OVERLAPPABLE #-} (HTclObjCvt a) => HTclObjCvt [a] where
    toHTObj ls = TLst $ map toHTObj ls


-- HTclObj utilities
tag :: String -> [HTclObj] -> HTclObj
tag s os = TLst ((TStr s):os)

tagStr :: String -> String -> HTclObj
tagStr t s = TLst [TStr t, TStr s]

tagInt :: String -> Int -> HTclObj
tagInt t n = TLst [TStr t, TInt n]

tagLst :: String -> [HTclObj] -> HTclObj
tagLst s os = TLst [TStr s, TLst os]

tagManyStr :: String -> [String] -> HTclObj
tagManyStr t ss = tagLst t (map TStr ss)

tagManyInt :: String -> [Int] -> HTclObj
tagManyInt t ss = tagLst t (map TInt ss)

joinHTObj :: HTclObj -> HTclObj -> HTclObj
joinHTObj (TLst xs) (TLst ys) = TLst (xs ++ ys)
joinHTObj (TLst xs) y         = TLst (xs ++ [y])
joinHTObj x (TLst ys)         = TLst ([x] ++ ys)
joinHTObj x y                 = TLst [x, y]

joinHTObjs :: HTclObj -> [HTclObj] -> HTclObj
joinHTObjs = foldl joinHTObj

--------------------------------------------------------------------------------
-- These function do the right conversion or return Nothing.
-- Works on a single TclObj

htclPObjToMInt :: TclInterp -> PTclObj -> IO (Maybe Int)
htclPObjToMInt interp po = do
  alloca (\pint -> do
            stat <- tcl_GetIntFromObj interp po pint
            case stat of
              0 -> peek pint >>= (return . Just . castI)
              _ -> return Nothing
         )

htclPObjToMWordPtr :: TclInterp -> PTclObj -> IO (Maybe WordPtr)
htclPObjToMWordPtr interp po = do
  alloca (\pint -> do
            stat <- tcl_GetLongFromObj interp po pint
            case stat of
              0 -> peek pint >>= (return . Just . castI)
              _ -> return Nothing
         )

htclPObjToMBool :: TclInterp -> PTclObj -> IO (Maybe Bool)
htclPObjToMBool interp po = do
  alloca (\pbool -> do
            stat <- tcl_GetBooleanFromObj interp po pbool
            case stat of
              0 -> do cint <- peek pbool
                      return $ Just ((castI cint) /= (0 :: Integer))
              _ -> return Nothing
         )

htclPObjToMDouble :: TclInterp -> PTclObj -> IO (Maybe Double)
htclPObjToMDouble interp po = do
  alloca (\pdbl -> do
            stat <- tcl_GetDoubleFromObj interp po pdbl
            case stat of
              0 -> peek pdbl >>= (return . Just . castD )
              _ -> return Nothing
         )

htclPObjToMString :: TclInterp -> PTclObj -> IO (Maybe String)
htclPObjToMString interp pobj = do
  alloca (\pint -> do
            --x0 <- peek pint
            --putStrLn $ " string to maybe: " ++ show pint ++ " " ++ show x0
            pc <- tcl_GetStringFromObj pobj pint
            --        x <- peek pint
            --putStrLn $ "grabbed the string to maybe: " ++ show pc ++ " " ++ show pint ++ " " ++ show x  ++ " 0x" ++ ((showHex x) "" )
            --let size = x `mod`  (4294967296)
            if (pc == nullPtr) then
                return Nothing
             else peek pint >>= (\i -> peekCStringLen (pc,castI i)) >>= (return . Just)
         )

htclPObjToMList :: TclInterp -> PTclObj -> IO (Maybe [TclObj])
htclPObjToMList interp po = do
  alloca (\pint -> do
            alloca (\pa -> do
                      stat <- tcl_ListObjGetElements interp po pint pa
                      if (stat /= htcl_OKc ) then return Nothing
                       else do
                             objc <- peek pint >>= return . castI
                             objv <- peek pa
                             peekArray objc objv >>= mapM wrapPtrForExport >>= (return . Just)
                   )
         )


htclObjToMInt :: TclInterp -> TclObj -> IO (Maybe Int)
htclObjToMInt interp o = do
  withForeignPtr o (\op -> htclPObjToMInt interp op )

htclObjToMWordPtr :: TclInterp -> TclObj -> IO (Maybe WordPtr)
htclObjToMWordPtr interp o = do
  withForeignPtr o (\op -> htclPObjToMWordPtr interp op )

htclObjToMBool :: TclInterp -> TclObj -> IO (Maybe Bool)
htclObjToMBool interp o = do
  withForeignPtr o (\op -> htclPObjToMBool interp op)

htclObjToMDouble :: TclInterp -> TclObj -> IO (Maybe Double)
htclObjToMDouble interp o = do
  withForeignPtr o (\op -> htclPObjToMDouble interp op )

htclObjToMString :: TclInterp -> TclObj -> IO (Maybe String)
htclObjToMString interp obj = do
  withForeignPtr obj (htclPObjToMString interp)

htclObjToMList :: TclInterp -> TclObj -> IO (Maybe [TclObj])
htclObjToMList interp obj = do
  withForeignPtr obj (htclPObjToMList interp)

--------------------------------------------------------------------
--
htclArgsToTcl :: TclInterp -> Int -> PTclObjArray -> IO [TclObj]
htclArgsToTcl interp objc objv = do
  peekArray objc objv >>= mapM wrapPtrForExport


-------------------------------------------------------------
-- Coversion which throw errors on the IO monad

htclPObjToInt :: TclInterp -> PTclObj -> IO Int
htclPObjToInt interp po = do
  alloca (\pint -> do
            stat <- tcl_GetIntFromObj interp po pint
            case stat of
              0 -> peek pint  >>= (return . castI)
              _ -> ioError (userError "")
         )

htclPObjToBool :: TclInterp -> PTclObj -> IO Bool
htclPObjToBool interp po = do
  alloca (\pint -> do
            stat <- tcl_GetBooleanFromObj interp po pint
            case stat of
              0 -> peek pint  >>= (return . toBool)
              _ -> ioError (userError "")
         )

htclPObjToDouble :: TclInterp -> PTclObj -> IO Double
htclPObjToDouble interp po = do
  alloca (\pdbl -> do
            stat <- tcl_GetDoubleFromObj interp po pdbl
            case stat of
              0 -> peek pdbl >>= return . castD
              _ -> ioError (userError "")
         )

htclPObjToString :: TclInterp -> PTclObj -> IO (String)
htclPObjToString interp pobj = do
  alloca (\pint -> do
            pc <- tcl_GetStringFromObj pobj pint
            if (pc == nullPtr) then
                ioError (userError "")
             else peek pint >>= (\i -> peekCStringLen (pc,castI i))
         )

htclPObjToList :: TclInterp -> PTclObj -> IO [TclObj]
htclPObjToList interp po = do
  alloca (\pint -> do
            alloca (\pa -> do
                      stat <- tcl_ListObjGetElements interp po pint pa
                      if (stat /= htcl_OKc ) then ioError (userError "")
                       else do
                             objc <- peek pint >>= return . castI
                             objv <- peek pa
                             peekArray objc objv >>= mapM wrapPtrForExport
                   )
         )


--  function on TclObjs
htclObjToInt :: TclInterp -> TclObj -> IO Int
htclObjToInt i o = withForeignPtr o (htclPObjToInt i)

htclObjToBool :: TclInterp -> TclObj -> IO Bool
htclObjToBool i o = withForeignPtr o (htclPObjToBool i)

htclObjToDouble :: TclInterp -> TclObj -> IO Double
htclObjToDouble i o = withForeignPtr o (htclPObjToDouble i)

htclObjToString :: TclInterp -> TclObj -> IO String
htclObjToString i o = withForeignPtr o (htclPObjToString i)

htclObjToList :: TclInterp -> TclObj -> IO [TclObj]
htclObjToList i o = withForeignPtr o (htclPObjToList i)


-- Converting to List of T, etc.
-- Note that errors are thrown
htclObjToListInt :: TclInterp -> TclObj -> IO [Int]
htclObjToListInt i o = htclObjToList i o >>= mapM (htclObjToInt i)

htclObjToListDouble :: TclInterp -> TclObj -> IO [Double]
htclObjToListDouble i o = htclObjToList i o >>= mapM (htclObjToDouble i)

htclObjToListString :: TclInterp -> TclObj -> IO [String]
htclObjToListString i o = htclObjToList i o >>= mapM (htclObjToString i)

--------------------------------------------------------------------------------
-- Utility functions for generating error messages when checking command grammar

cmdExtraArgs :: [String] -> IO a
cmdExtraArgs args =
  let msg = "Unexpected additional arguments: \"" ++ (unwords args) ++ "\"."
  in ioError $ userError msg

cmdTooShort :: HTclCmdGrammar -> IO a
cmdTooShort g =
  let msg = unlines [ "Command is incomplete.  It is expected to continue with:"
                    , (htclDescribeCmdGrammar g 79)
                    ]
  in ioError $ userError msg

cmdBadSyntax :: [String] -> HTclCmdGrammar -> IO a
cmdBadSyntax args g =
   let msg = unlines [ "Command is invalid.  At \"" ++ (unwords args) ++ "\" expected:"
                     , (htclDescribeCmdGrammar g 79)
                     ]
  in ioError $ userError msg

--------------------------------------------------------------------------------
