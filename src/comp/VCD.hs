{-# LANGUAGE CPP #-}
module VCD ( VCD, parseVCD, parseVCDSize, formatVCD
           , VCDCmd(..), Code, VCDBitType(..), VCDValue(..)
           , VCDChangeEntry, signal_code, new_value
           , SignalType(..), ScopeType
           , vcd_code_to_string
           , vcd_is_true_bit, vcd_is_x, vcd_is_z, vcd_to_integer
           , to_VCDValue, to_X_VCDValue
           ) where

-- This is a simple VCD file parsing and writing utility.
--
-- It is designed to treat VCD files as a list of individual VCD
-- commands, with the idea that the list can be lazily constructed and
-- incrementally produced.  This is a good approach for a stream-based
-- transformation of VCD files that are too large to fit in memory.
--
-- This mechanism is *NOT* suited to random access to a VCD waveform.
-- If you need that, then you will have to write a more complex
-- library that seeks around in the VCD file and pages data in and out
-- as needed.
--
-- Although not tuned to perfection, this implementation uses lazy
-- byte-strings and attempts to be relatively efficient, since VCD
-- files can be enormous.

import Data.Char
import Data.Time
import Data.List(unfoldr, isPrefixOf, mapAccumL)
import Data.Bits
import qualified Data.ByteString.Lazy.Char8 as C
import Numeric(showGFloat)

-- import Debug.Trace

-- --------
-- Basic VCD data structures

-- VCD identifier code
type Code = Integer

-- VCD binary data is represented as 0, 1, X or Z
data VCDBitType = Logic Bool | X | Z
  deriving (Eq,Ord)

-- Values are represented differently for scalars, vectors and reals
data VCDValue = Scalar VCDBitType
              | Vector [VCDBitType]
              | Real Double
  deriving (Eq,Ord)

instance Show VCDValue where
  show (Scalar b) = [vcd_bit_to_char b]
  show (Vector bs) = 'b':(map vcd_bit_to_char bs)
  show (Real r) = 'r':(showGFloat Nothing r "")

vcd_is_true_bit :: VCDValue -> Bool
vcd_is_true_bit (Scalar (Logic True)) = True
vcd_is_true_bit _                     = False

vcd_is_x :: VCDValue -> Bool
vcd_is_x (Scalar X)  = True
vcd_is_x (Vector bs) = all (== X) bs
vcd_is_x _           = False

vcd_is_z :: VCDValue -> Bool
vcd_is_z (Scalar Z)  = True
vcd_is_z (Vector bs) = all (== Z) bs
vcd_is_z _           = False

vcd_to_integer :: VCDValue -> Maybe Integer
vcd_to_integer (Scalar (Logic b)) = Just (if b then 1 else 0)
vcd_to_integer (Vector bs) =
    let bs' = [ if b then 1 else 0 | (Logic b) <- bs ]
        num_bs = length bs
        num_bs' = length bs'
    in if (num_bs == num_bs')
       then Just (sum $ zipWith (\n e -> n*(2^e)) bs' [(num_bs'-1),(num_bs'-2)..0])
       else Nothing
vcd_to_integer _ = Nothing

to_VCDValue :: (Integral a) => a -> Integer -> VCDValue
to_VCDValue 0 _ = Scalar X
to_VCDValue 1 n = Scalar (Logic (n /= 0))
to_VCDValue w n =
  let x = fromIntegral w
      bits = dropWhile (== False) [ (testBit n pos) | pos <- [x-1,x-2..0] ]
  in if (null bits) then Vector [Logic False] else Vector (map Logic bits)

to_X_VCDValue :: (Integral a) => a -> VCDValue
to_X_VCDValue 0 = Scalar X
to_X_VCDValue 1 = Scalar X
to_X_VCDValue w = Vector [X]

-- A change is an identifier code and its new value
type VCDChangeEntry = (Code,VCDValue)

signal_code :: VCDChangeEntry -> Code
signal_code = fst

new_value :: VCDChangeEntry -> VCDValue
new_value = snd

-- VCD signal types
data SignalType = Reg | Wire | Integer | Float
  deriving (Eq,Ord)

instance Show SignalType where
  show Reg     = "reg"
  show Wire    = "wire"
  show Integer = "integer"
  show Float   = "real"

-- VCD scope types
data ScopeType = Module
               | Begin
               | Function
  deriving (Eq,Ord)

instance Show ScopeType where
  show Module   = "module"
  show Begin    = "begin"
  show Function = "function"

-- These are the various entities that can occur in a VCD file.
data VCDCmd = Comment String
            | Date String (Maybe UTCTime)
            | Timescale Integer Integer
            | Scope ScopeType String
            | UpScope
            | Var SignalType Integer Code String
            | Version String
            | Task String [VCDChangeEntry]
            | EndDefs
            | Timestamp Integer
            | Change VCDChangeEntry
            | VCDErr String String
  deriving (Eq,Ord)

-- The sequence of VCDCmds makes up the entire contents of the VCD file.
-- An unchecked invariant is that only Task, Timestamp, Comment and Change
-- commands occur after the (single) EndDefs command in the list.
type VCD = [VCDCmd]

-- -------
-- A parser for reading a VCD file

type Token = (Integer,C.ByteString)

tokenize :: C.ByteString -> [Token]
tokenize s = [ (n,w)
             | (n,w) <- snd $ mapAccumL addLen (0::Integer) (C.splitWith isSpace s)
             , not (C.null w)
             ]
  where addLen l w = let l' = l + (fromIntegral (C.length w)) + 1
                     in (l',(l,w))

parseVCD :: C.ByteString -> VCD
parseVCD s = map fst $ parseVCDSize s

parseVCDSize :: C.ByteString -> [(VCDCmd,Integer)]
parseVCDSize s = unfoldr parser (tokenize s)

parser :: [Token] -> Maybe ((VCDCmd,Integer),[Token])
parser []     = Nothing
parser ((l,w):ws) =
    let (c,rest) = (C.head w, C.tail w)
        (cmd,ws') =
            case c of
              '$' -> parseCommand rest ws
              '#' -> (readTimestamp rest, ws)
              _   -> if (c `C.elem` (C.pack "01XxZz"))
                     then (readScalar w, ws)
                     else if (c == 'b' || c == 'B')
                          then parseVector rest ws
                          else if (c == 'r' || c == 'R')
                               then parseReal rest ws
                               else (error_p "invalid command" (w:(map snd ws)), [])
        count = case ws' of
                  []         -> fromIntegral (C.length w)
                  ((l',_):_) -> l' - l
    in if ((cmd,count) == (cmd,count)) -- force thunks
       then Just ((cmd,count),ws')
       else error "not good"

-- Parser for VCD commands
parseCommand :: C.ByteString -> [Token] -> (VCDCmd,[Token])
parseCommand name [] = (error_p ("no $end for " ++ (C.unpack name)) [], [])
parseCommand name ws =
    let (body,rest) = break (\(_,x) -> x == (C.pack "$end")) ws
    in if (null rest)
       then (error_p ("no $end for " ++ (C.unpack name)) (map snd ws), [])
       else let rest' = tail rest
                p = get_parser name
            in (p (map snd body), rest')
  where get_parser n = case (C.unpack n) of
                        "comment"        -> comment_p
                        "date"           -> date_p
                        "version"        -> version_p
                        "timescale"      -> timescale_p
                        "scope"          -> scope_p
                        "var"            -> var_p
                        "upscope"        -> upscope_p
                        "enddefinitions" -> enddefs_p
                        x                -> if ("dump" `isPrefixOf` x)
                                            then task_p x
                                            else error_p $ "invalid task name '" ++ (C.unpack n) ++ "'"

-- create a Comment command
comment_p :: [C.ByteString] -> VCDCmd
comment_p ws = Comment (C.unpack (C.unwords ws))

-- create a Date command
date_p :: [C.ByteString] -> VCDCmd
date_p ws = let s = C.unpack (C.unwords ws)
                parseFn l f s = parseTimeM True l f s
            in Date s (parseFn defaultTimeLocale rfc822DateFormat s)

-- create a Version command
version_p :: [C.ByteString] -> VCDCmd
version_p ws = Version (C.unpack (C.unwords ws))

-- create a Timescale command
timescale_p :: [C.ByteString] -> VCDCmd
timescale_p [n,u] = Timescale (read (C.unpack n)) (readTimeUnit (C.unpack u))
timescale_p [x]   = let (n,u) = C.span isDigit x
                    in timescale_p [n,u]
timescale_p ws    = error_p "bad timescale" ws

readTimeUnit :: String -> Integer
readTimeUnit "s"  = 0
readTimeUnit "ms" = 3
readTimeUnit "us" = 6
readTimeUnit "ns" = 9
readTimeUnit "ps" = 12
readTimeUnit "fs" = 18
readTimeUnit "as" = 21
readTimeUnit x    = error $ "bad time unit " ++ x

-- create a Scope command
scope_p :: [C.ByteString] -> VCDCmd
scope_p [t,n] = case (readScopeType (C.unpack t)) of
                  Just t' -> Scope t' (C.unpack n)
                  Nothing -> error_p "unknown scope type" [t,n]
scope_p ws    = error_p "invalid scope command" ws

readScopeType :: String -> Maybe ScopeType
readScopeType "module"   = Just Module
readScopeType "begin"    = Just Begin
readScopeType "function" = Just Function
readScopeType _          = Nothing

-- create a Var command
var_p :: [C.ByteString] -> VCDCmd
var_p [t,w,c,n] = case (readSignalType (C.unpack t)) of
                    Just t' -> Var t' (read (C.unpack w)) (parse_vcd_code c) (C.unpack n)
                    Nothing -> error_p "unknown var type" [t,w,c,n]
var_p [t,w,c,n,sz] = var_p [t,w,c,n]
var_p ws = error_p "invalid var command" ws

readSignalType :: String -> Maybe SignalType
readSignalType "reg"     = Just Reg
readSignalType "wire"    = Just Wire
readSignalType "integer" = Just Integer
readSignalType "real"    = Just Float
readSignalType _         = Nothing

-- create an UpScope command
upscope_p :: [C.ByteString] -> VCDCmd
upscope_p [] = UpScope
upscope_p ws = error_p "invalid upscope command" ws

-- create an EndDefs command
enddefs_p :: [C.ByteString] -> VCDCmd
enddefs_p [] = EndDefs
enddefs_p ws = error_p "invalid enddefinitions command" ws

-- create a Task command with its included value changes
task_p :: String -> [C.ByteString] -> VCDCmd
task_p tsk ws =
    case (readChanges ws) of
      (Left xs)    -> error_p ("in task " ++ tsk) xs
      (Right chgs) -> Task tsk chgs

readChanges :: [C.ByteString] -> Either [C.ByteString] [VCDChangeEntry]
readChanges [] = Right []
readChanges (w:ws) =
  let (c,rest) = (C.head w, C.tail w)
  in if (c `C.elem` (C.pack "01XxZz"))
     then case (readChanges ws) of
            (Left err) -> Left err
            (Right xs) -> Right ((scalar_p w):xs)
     else
       case ws of
         (w':ws') ->
          let mx = if (c == 'b' || c == 'B')
                   then Just (vector_p rest w')
                   else if (c == 'r' || c == 'R')
                        then Just (real_p rest w')
                        else Nothing
          in case (mx, readChanges ws') of
               (Nothing, _)       -> Left (w:ws)
               (_,Left err)       -> Left err
               (Just x, Right xs) -> Right (x:xs)
         _ -> Left (w:ws)

-- create an Err command
error_p :: String -> [C.ByteString] -> VCDCmd
error_p msg ws = VCDErr msg (C.unpack (C.unwords (take 5 ws)))

-- read a timestamp
readTimestamp :: C.ByteString -> VCDCmd
readTimestamp s = Timestamp (read (C.unpack s))

-- read a scalar value change
readScalar :: C.ByteString -> VCDCmd
readScalar w = Change (scalar_p w)

scalar_p :: C.ByteString -> VCDChangeEntry
scalar_p w = let (b,c) = (C.head w, C.tail w)
             in (parse_vcd_code c, Scalar (parse_vcd_bit b))

-- parse a vector value change
parseVector :: C.ByteString -> [Token] -> (VCDCmd,[Token])
parseVector w [] = (error_p "missing signal code in vector change" [w], [])
parseVector w ((_,c):rest) = (Change (vector_p w c), rest)

vector_p :: C.ByteString -> C.ByteString -> VCDChangeEntry
vector_p v c =
    let b0 = C.head v
        rest = C.tail v
        trim b s | (C.null s) = [parse_vcd_bit b]
                 | (b /= '1' && b == (C.head s)) = trim b (C.tail s)
                 | otherwise = map parse_vcd_bit (b:(C.unpack s))
    in (parse_vcd_code c, Vector (trim b0 rest))

-- parse a real value change
parseReal :: C.ByteString -> [Token] -> (VCDCmd,[Token])
parseReal w [] = (error_p "missing signal code in real change" [w], [])
parseReal w ((_,c):rest) = (Change (real_p w c), rest)

real_p :: C.ByteString -> C.ByteString -> VCDChangeEntry
real_p r c = (parse_vcd_code c, Real (read (C.unpack r)))

-- Parse a string representing a VCD identifier code
buildUp :: ((Integer,Char) -> Integer) -> Integer -> C.ByteString -> Integer
buildUp f x s = if (C.null s)
                then x
                else buildUp f (f (x,C.head s)) (C.tail s)

take_char :: (Integer,Char) -> Integer
take_char (n,c) = (n * 94) + fromIntegral((ord c) - (ord '!'))

parse_vcd_code :: C.ByteString -> Code
parse_vcd_code s = buildUp take_char 0 s

-- Parse one bit
parse_vcd_bit :: Char -> VCDBitType
parse_vcd_bit '0' = Logic False
parse_vcd_bit '1' = Logic True
parse_vcd_bit 'x' = X
parse_vcd_bit 'X' = X
parse_vcd_bit 'z' = Z
parse_vcd_bit 'Z' = Z
parse_vcd_bit x   = error $ "invalid bit char " ++ (show x)

-- --------
-- A writer for formatting VCD data

formatVCD :: VCD -> String
formatVCD vcd = unlines $ concatMap fmt vcd
  where fmt (Comment s) = ["$comment", s, "$end"]
        fmt (Date s _)  = ["$date", "    " ++ s, "$end"]
        fmt (Version s) = ["$version", "    " ++ s, "$end"]
        fmt (Timescale n u) = ["$timescale", "    " ++ formatTimescale (n,u), "$end"]
        fmt (Scope t n) = ["$scope " ++ (show t) ++ " " ++ n ++ " $end"]
        fmt (Var t w c n) = ["$var " ++ (show t) ++ " " ++
                                        (show w) ++ " " ++
                                        (vcd_code_to_string c) ++ " " ++
                                        n ++ " $end"]
        fmt UpScope = ["$upscope $end"]
        fmt EndDefs = ["$enddefinitions $end"]
        fmt (Timestamp t) = ['#':(show t)]
        fmt (Change vc) = [value_change_to_string vc]
        fmt (Task tsk chgs) = ['$':tsk] ++
                              (map value_change_to_string chgs) ++
                              ["$end"]
        fmt (VCDErr msg txt) = ["ERROR: " ++ msg ++ " in '" ++ txt ++ "'"]

-- Convert timescale to string
formatTimescale :: (Integer,Integer) -> String
formatTimescale (n,u) =
    if (u `mod` 3 == 0)
    then (show n) ++ " " ++ (fmtUnit u)
    else formatTimescale (10*n,u-1)
  where fmtUnit 0  = "s"
        fmtUnit 3  = "ms"
        fmtUnit 6  = "us"
        fmtUnit 9  = "ns"
        fmtUnit 12 = "ps"
        fmtUnit 18 = "fs"
        fmtUnit 21 = "as"
        fmtUnit n  = error $ "fmtUnit: " ++ (show n)

-- Convert a VCD identifier code to a string
vcd_code_to_string :: Code -> String
vcd_code_to_string 0 = "!"
vcd_code_to_string n = helper n []
  where helper 0 cs = cs
        helper x cs = let (q,r) = x `quotRem` 94
                      in helper q ((to_chr r):cs)
        to_chr x = chr ((ord '!') + (fromInteger x))

-- Convert a bit to its character
vcd_bit_to_char :: VCDBitType -> Char
vcd_bit_to_char (Logic b) = if b then '1' else '0'
vcd_bit_to_char X         = 'x'
vcd_bit_to_char Z         = 'z'

-- Get the string for a change entry (code + new value)
value_change_to_string :: VCDChangeEntry -> String
value_change_to_string (code, Scalar b) =
    (vcd_bit_to_char b):(vcd_code_to_string code)
value_change_to_string (code, Vector bs) =
    unwords ['b':(map vcd_bit_to_char bs), vcd_code_to_string code]
value_change_to_string (code, Real r) =
    unwords ['r':(showGFloat Nothing r ""), vcd_code_to_string code]
