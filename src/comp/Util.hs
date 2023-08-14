{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Util where

import Data.Char(intToDigit)
import Data.Word(Word8,Word32,Word64)
import Data.Bits
import Data.List(sort, sortBy, group, groupBy, nubBy, union, foldl')
import Data.Bifunctor(first,second)
import Control.Monad(foldM)
import Debug.Trace(trace)
import qualified Data.Set as S
import qualified Data.Map as M
-- import Numeric(showHex)

import ErrorUtil(internalError)
import qualified Log2
import Sort(sortLe)

-- Note:
--   There are some list functions in Libs/ListUtil.hs
--   They could be consolidated with this file.


-- =====
-- Not-to-be-checked-in trace functions

{-
import System.IO.Unsafe(unsafePerformIO)
import IO(hPutStr, hFlush, stderr)
import IOUtil(progArgs)

doTrace = elem "-trace--debug" progArgs
doTrace2 = length (filter (== "-trace-debug") progArgs) > 1
doFull = elem "-trace-full" progArgs

tracex s x = if doTrace then traces s x else x
tracex2 s x = if doTrace2 then traces s x else x

traceChars :: String -> a -> a
traceChars cs x = unsafePerformIO (hPutStr stderr cs >> hFlush stderr >> return x)
-}

-- =====
-- Common trace functions used in other modules

traces :: String -> a -> a
traces s x = if s==s then trace s x else internalError "Util.traces"

tracep :: Bool -> String -> p -> p
tracep p s x = if p then traces s x else x

-- lets you peek at the answer to a computation
-- e.g. "trace_answer (\x -> "answer is " ++ (show x)) (2+2)
trace_answer :: (a -> String) -> a -> a
trace_answer format x =
   trace (format x) $ x

-- =====
-- Configurable traces
-- (currently only used in Id and XRef)

dbgLevel :: Int
dbgLevel = -1

-- =====
-- Internal compiler assertions

assert :: Bool -> [Char] -> p -> p
assert True msg v = v
assert False msg v = internalError ("assertion failed: "++msg)


-- =====
-- String utilities

quote :: String -> String
quote s = "`" ++ s ++ "'"

doubleQuote :: String -> String
doubleQuote s = "\"" ++ s ++ "\""


unwordsAnd, unwordsOr :: [String] -> String
unwordsAnd = unwordsx "and"
unwordsOr = unwordsx "or"

unwordsx :: String -> [String] -> String
unwordsx _ [] = ""
unwordsx _ [x] = x
unwordsx s [x1, x2] = unwords [x1, s, x2]
unwordsx s xs = unwordsWith ", " (init xs++[s++" "++last xs])

unwordsWith :: String -> [String] -> String
unwordsWith d [] = ""
unwordsWith d [x] = x
unwordsWith d (x:xs) = x++d++unwordsWith d xs

readOrErr :: (Read a) => String -> String -> a
readOrErr err s = fst $ headOrErr err $ reads s

-- =====
-- ToString class

class ToString a where
    to_string :: a -> String
    itos :: a -> String

instance ToString Int where
    itos a = show a
    to_string a = internalError ("to_string applied to nonsymbol (Int) "
                                    ++ show a)

instance ToString Integer where
    itos a = show a
    to_string a = internalError ("to_string applied to nonsymbol (Integer) "
                                    ++ show a)

instance ToString Char where
    itos a = show a
    to_string a = case a of
        '\n' -> "\\n"
        '\r' -> "\\r"
        '\t' -> "\\t"
        '\a' -> "\\a"
        '\\' -> "\\\\"
        '"' -> "\\\""        -- backslash double-quote
        _ | n < 0 ||
            n > 0x100 -> internalError "quoting a character value " ++ show n
        _ | n < 0x20 || n >= 0x7F ->
            [ '\\', intToDigit highest, intToDigit middle, intToDigit lowest ]
        _ -> [a]
      where
        n = fromEnum a
        (top2, lowest) = quotRem n 8
        (highest, middle) = quotRem top2 8

instance ToString String where
    itos a = internalError "itos applied to string" ++ show a
    to_string a = concatMap to_string a

to_quoted_string :: ToString a => a -> String
to_quoted_string s = "\"" ++ to_string s ++ "\""


-- =====
-- List utilities

headOrErr :: String -> [elem] -> elem
headOrErr _   (elt:_) = elt
headOrErr err []      = internalError err

tailOrErr :: String -> [elem] -> [elem]
tailOrErr _   (_:rest) = rest
tailOrErr err []       = internalError err

initOrErr :: String -> [elem] -> [elem]
initOrErr _   [x]    = []
initOrErr err (x:xs) = x : initOrErr err xs
initOrErr err []     = internalError err

lastOrErr :: String -> [elem] -> elem
lastOrErr _   [x]    = x
lastOrErr err (_:xs) = lastOrErr err xs
lastOrErr err []     = internalError err

unconsOrErr :: String -> [elem] -> (elem, [elem])
unconsOrErr _   (elt:rest) = (elt, rest)
unconsOrErr err []         = internalError err

take2OrErr :: String -> [elem] -> (elem, elem)
take2OrErr _ (x1:x2:_) = (x1, x2)
take2OrErr err _ = internalError err

take3OrErr :: String -> [elem] -> (elem, elem, elem)
take3OrErr _ (x1:x2:x3:_) = (x1, x2, x3)
take3OrErr err _ = internalError err

rTake, rDrop :: Int -> [a] -> [a]
rTake n = reverse . take n . reverse
rDrop n = reverse . drop n . reverse

unions :: (Foldable t, Eq a) => t [a] -> [a]
unions l = foldr union [] l

concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f as = do
  temp <- mapM f as
  return (concat temp)

-- Haskell Prelude definition says that this is the same as "any (eq x)"
elemBy                        :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy eq _ []                = False
elemBy eq x (y:ys)        = eq x y || elemBy eq x ys

findSame :: (Ord a) => [a] -> [[a]]
findSame = filter ((>1) . length) . group . sort

findSameBy :: (a -> a -> Ordering) -> (a -> a -> Bool) -> [a] -> [[a]]
findSameBy sortFn groupFn =
    filter ((>1) . length) . (groupBy groupFn) . (sortBy sortFn)

toMaybe :: Bool -> a -> Maybe a
toMaybe False _ = Nothing
toMaybe True a = Just a

-- A O(n^2) function to find duplicate entries in a list
-- appears to find the first duplicated entry and then return it as a list
findDup :: (Eq a) => [a] -> [a]
findDup [] = []
findDup (x:xs) =
    case filter (== x) xs of
    [] -> findDup xs
    xs' -> x:xs'

sortGroup :: (a->a->Bool) -> [a] -> [[a]]
sortGroup le = groupBy (\x y-> le x y && le y x) . sortLe le

mergeWithCmp ::  (a -> a -> Ordering) -> (a -> a -> a) -> [a] -> [a] -> [a]
mergeWithCmp _  _ xs [] = xs
mergeWithCmp _  _ [] ys = ys
mergeWithCmp cmp f xxs@(x:xs) yys@(y:ys) =
    case x `cmp` y of
        EQ -> f x y : mergeWithCmp cmp f xs ys
        LT -> x : mergeWithCmp cmp f xs yys
        GT -> y : mergeWithCmp cmp f xxs ys

isOrdSubset :: (Ord a) => [a] -> [a] -> Bool
isOrdSubset [] _  = True
isOrdSubset _  [] = False
isOrdSubset xxs@(x:xs) (y:ys) =
    case compare x y of
    LT -> False
    EQ -> isOrdSubset xs ys
    GT -> isOrdSubset xxs ys

remOrdDup :: (Eq a) => [a] -> [a]
remOrdDup (x:xxs@(x':_)) | x == x' = remOrdDup xxs
remOrdDup (x:xs) = x : remOrdDup xs
remOrdDup [] = []

mergeOrdNoDup :: (Ord a) => [a] -> [a] -> [a]
mergeOrdNoDup xxs@(x:xs) yys@(y:ys) =
    case compare x y of
    LT -> x : mergeOrdNoDup xs yys
    GT -> y : mergeOrdNoDup xxs ys
    EQ -> x : mergeOrdNoDup xs ys
mergeOrdNoDup []         yys = yys
mergeOrdNoDup xxs        []  = xxs

-- removes duplicates faster than nub
-- by using a sorted set (so it reorders elements)
fastNub :: (Ord a) => [a] -> [a]
fastNub = S.toList . S.fromList

-- if you intend to sort and nub, you can be more efficient
nubSort :: (Ord a) => [a] -> [a]
nubSort = map head . group . sort

stableOrdNub :: (Ord a) => [a] -> [a]
stableOrdNub = stableOrdNub' S.empty
  where stableOrdNub' _ [] = []
        stableOrdNub' s (a:as)
          | a `S.member` s  = stableOrdNub' s as
          | otherwise = a : stableOrdNub' (S.insert a s) as

-- =====
-- Boolean List utilities

boolCompress :: [Bool] -> [a] -> [a]
boolCompress [] _  = []
boolCompress _  [] = []
boolCompress (True:bs) (x:xs) = x : boolCompress bs xs
boolCompress (False:bs) (x:xs) = boolCompress bs xs

anySame :: (Ord a) => [a] -> Bool
anySame = same . sort
        where same (x:xs@(x':_)) = x == x' || same xs
              same _ = False

allSame :: (Eq a) => [a] -> Bool
allSame [] = True
allSame (x:xs) = all (==x) xs


-- =====
-- List/Tuple utilities

unzipWith :: (a -> (b,c)) -> [a] -> ([b], [c])
unzipWith f l = unzip (map f l)

concatUnzipMap :: (a -> ([b],[c])) -> [a] -> ([b],[c])
concatUnzipMap f zs =
        let (xss, yss) = unzip (map f zs)
        in  (concat xss, concat yss)

concatUnzip :: [([a],[b])] -> ([a],[b])
concatUnzip xys =
    let (xss, yss) = unzip xys
    in  (concat xss, concat yss)

concatUnzip3 :: [([a],[b],[c])] -> ([a],[b],[c])
concatUnzip3 xyzs =
    let (xss, yss, zss) = unzip3 xyzs
    in  (concat xss, concat yss, concat zss)

mapFst :: Functor f => (a -> b) -> f (a, c) -> f (b, c)
mapFst = fmap . first

mapSnd :: Functor f => (a -> b) -> f (c, a) -> f (c, b)
mapSnd = fmap . second

mapThd :: (t -> c) -> [(a, b, t)] -> [(a, b, c)]
mapThd f xyzs = [(x, y, f z) | (x, y, z) <- xyzs]

joinByFst :: (Ord a) => [(a, b)] -> [(a, [b])]
joinByFst =
  let joinSameFirst xys@((x,_):_) = (x, map snd xys)
      joinSameFirst _ = internalError "joinByFst"
  in
    map joinSameFirst .
    groupBy (\ (x,_) (y,_) -> x==y) .
    sortBy (\ (x,_) (y,_) -> x `compare` y)

mergeWith :: (Ord b) => (a -> a -> a) -> [(b, a)] -> [(b, a)] -> [(b, a)]
mergeWith f = mergeWithCmp cmpFst f'
    where f' (k,v) (_,v') = (k, v `f` v')

flattenPairs :: [(a,a)] -> [a]
flattenPairs [] = []
flattenPairs ((x,y):xys) = x:y:flattenPairs xys

makePairs :: [a] -> [(a,a)]
makePairs [] = []
makePairs (x:y:xs) = (x, y) : makePairs xs
makePairs _ = internalError "Util.makePairs: failed"

-- all pairs except pairs of an item with itself
allPairs :: [a] -> [(a, a)]
allPairs [] = []
allPairs (x:xs) = concat [[(x,x'), (x',x)] | x' <- xs] ++ allPairs xs

-- all unique pairs -- i.e. only one of (x,y) and (y,x)
uniquePairs :: [a] -> [(a, a)]
uniquePairs [] = []
uniquePairs (x:ys) = [(x,y) | y <- ys] ++ uniquePairs ys

-- all pairs of an item with itself
selfPairs :: [a] -> [(a, a)]
selfPairs xs = [(x, x) | x <- xs ]

mapFstM :: (Monad m) => (a -> m c) -> [(a, b)] -> m [(c, b)]
mapFstM f xs = mapM f' xs
  where f' (a, b) = f a >>= \ c -> return (c, b)

mapSndM :: (Monad m) => (b -> m c) -> [(a, b)] -> m [(a, c)]
mapSndM f xs = mapM f' xs
  where f' (a, b) = f b >>= \ c -> return (a, c)

appFstM :: (Monad m) => (a -> m c) -> (a, b) -> m (c , b)
appFstM f (a, b) = do c <- f a
                      return (c, b)

nubByFst :: (Eq a) => [(a, b)] -> [(a, b)]
nubByFst xs = nubBy f xs
  where f a b = (fst a == fst b)

sortPair :: (Ord a) => (a, a) -> (a, a)
sortPair (x, y) = if (y < x) then (y, x) else (x, y)

-- =====
-- List/Either utilities

checkEither :: [Either a b] -> Either [a] [b]
checkEither xs = f xs [] []
        where f [] [] rs = Right (reverse rs)
              f [] ls _  = Left  (reverse ls)
              f (Left l :xs) ls rs = f xs (l:ls) rs
              f (Right r:xs) ls rs = f xs ls (r:rs)

separate :: [Either a b] -> ([a],[b])
separate abs =
    let f (Left a)  (as, bs) = (a:as,   bs)
        f (Right b) (as, bs) = (  as, b:bs)
    in  foldr f ([],[]) abs


-- =====
-- List/Maybe utilities

fromJustOrErr :: String -> Maybe value -> value
fromJustOrErr err Nothing  = internalError err
fromJustOrErr _   (Just v) = v


-- =====
-- Tuple utilities

pair :: a -> b -> (a, b)
pair x y = (x, y)

swap :: (b, a) -> (a, b)
swap (x,y) = (y,x)

apFst :: (t -> a) -> (t, b) -> (a, b)
apFst f (x, y) = (f x, y)

apSnd :: (t -> b) -> (a, t) -> (a, b)
apSnd f (x, y) = (x, f y)

fst3 :: (a, b, c) -> a
fst3 (x,_,_) = x
snd3 :: (a, b, c) -> b
snd3 (_,x,_) = x
thd :: (a, b, c) -> c
thd (_,_,x) = x

fst2of3 :: (a, b, c) -> (a, b)
fst2of3 (x,y,_) = (x,y)

fth4 :: (a, b, c, d) -> d
fth4 (_,_,_,x) = x
fst2of4 :: (a, b, c, d) -> (a, b)
fst2of4 (x,y,_,_) = (x,y)
fst3of4 :: (a, b, c, d) -> (a, b, c)
fst3of4 (x,y,z,_) = (x,y,z)

ordPair :: Ord a => (a, a) -> (a, a)
ordPair (x,y) = if x < y then (x,y) else (y,x)

ordPairBy :: (a -> a -> Ordering) -> (a, a) -> (a, a)
ordPairBy cmp (x, y) = case (cmp x y) of
                         LT -> (x, y)
                         _  -> (y, x)

cmpFst :: Ord x => (x,y) -> (x,y) -> Ordering
cmpFst (a,_) (b,_) = compare a b

cmpSnd :: Ord y => (x,y) -> (x,y) -> Ordering
cmpSnd (_,a) (_,b) = compare a b

eqFst :: Eq x => (x,y) -> (x,y) -> Bool
eqFst (a,_) (b,_) = a == b

eqSnd :: Eq y => (x,y) -> (x,y) -> Bool
eqSnd (_,a) (_,b) = a == b


-- =====
-- Maybe utilities

fromMaybeM :: (Monad m) => m a -> m (Maybe a) -> m a
fromMaybeM def m = do
  mres <- m
  case mres of
    Nothing -> def
    Just res -> return res

-- =====
-- Either utilities

apLeft :: (a -> c) -> Either a b -> Either c b
apLeft f (Left x)  = Left (f x)
apLeft f (Right x) = Right x

apRight :: (b -> c) -> Either a b -> Either a c
apRight f (Left x)  = Left x
apRight f (Right x) = Right (f x)

doLeft :: (a -> Either c b) -> Either a b -> Either c b
doLeft f (Left x)  = f x
doLeft f (Right x) = Right x

doRight :: (b -> Either a c) -> Either a b -> Either a c
doRight f (Left x)  = Left x
doRight f (Right x) = f x

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight  _        = False

-- =====
-- Data.Map utilities

map_insertMany :: (Ord k) => [(k,a)] -> M.Map k a -> M.Map k a
map_insertMany kas m =
   foldr (uncurry M.insert) m kas

map_insertManyWith :: (Ord k) =>
                      (a -> a -> a) -> [(k,a)] -> M.Map k a -> M.Map k a
map_insertManyWith fn kas m =
   -- The choice of "foldr" is to match old OrdMap behavior
   foldr (uncurry (M.insertWith fn)) m kas

map_deleteMany :: (Ord k) => [k] -> M.Map k a -> M.Map k a
map_deleteMany ks m =
   foldr M.delete m ks

-- XXX this is probably inefficient; try using M.mapAccum
map_mapM :: (Ord k, Monad m) => (a -> m b) -> M.Map k a -> m (M.Map k b)
map_mapM fn m = mapSndM fn (M.toList m) >>= return . M.fromList

map_unionsWithM :: (Ord k, Monad m) =>
                   (a -> a -> m a) -> [M.Map k a] -> m (M.Map k a)
map_unionsWithM fn [] = return M.empty
map_unionsWithM fn [m] = return m
map_unionsWithM fn (m:ms) = foldM (map_unionWithM fn) m ms

map_unionWithM :: (Ord k, Monad m) =>
                  (a -> a -> m a) -> M.Map k a -> M.Map k a -> m (M.Map k a)
map_unionWithM fn m1 m2 = map_insertManyWithM fn (M.toList m2) m1

map_insertWithM :: (Ord k, Monad m) =>
                   (a -> a -> m a) -> k -> a -> M.Map k a -> m (M.Map k a)
map_insertWithM fn k a m =
    case (M.lookup k m) of
      Nothing -> return $ M.insert k a m
      Just b  -> do c <- fn a b
                    return $ M.insert k c m

map_insertManyWithM :: (Ord k, Monad m) =>
                       (a -> a -> m a) -> [(k, a)] -> M.Map k a -> m (M.Map k a)
map_insertManyWithM fn kas m =
    let insertOne m' (k, a) = map_insertWithM fn k a m'
    in  foldM insertOne m kas

map_insertWithKeyM ::
    (Ord k, Monad m) =>
    (k -> a -> a -> m a) -> k -> a -> M.Map k a -> m (M.Map k a)
map_insertWithKeyM fn k a m =
    case (M.lookup k m) of
      Nothing -> return $ M.insert k a m
      Just b  -> do c <- fn k a b
                    return $ M.insert k c m

map_insertManyWithKeyM ::
    (Ord k, Monad m) =>
    (k -> a -> a -> m a) -> [(k, a)] -> M.Map k a -> m (M.Map k a)
map_insertManyWithKeyM fn kas m =
    let insertOne m' (k, a) = map_insertWithKeyM fn k a m'
    in  foldM insertOne m kas

-- =====
-- Data.Set utilities

set_insertMany :: (Ord a) => [a] -> S.Set a -> S.Set a
set_insertMany as m = foldr S.insert m as

set_deleteMany :: (Ord a) => [a] -> S.Set a -> S.Set a
set_deleteMany as m = foldr S.delete m as

set_intersectMany :: (Ord a) => [S.Set a] -> S.Set a
set_intersectMany [] = S.empty
set_intersectMany ms = foldr1 S.intersection ms

-- =====
-- Numeric utilities

log2 :: (Integral a, Integral b) => a -> b
log2 = Log2.log2

divC :: Integer -> Integer -> Integer
divC x y = (x+y-1) `div` y

integerToBits :: Integer -> Integer -> [Integer]
integerToBits 0 0 = []
integerToBits 0 n = internalError "integerToBits"
integerToBits n i = integerToBits (n-1) q ++ [r]
  where (q, r) = i `quotRem` 2

integerSqrt :: Integer -> Maybe Integer
integerSqrt n =
    let n' :: Float
        n' = fromInteger n
        candidate :: Integer
        candidate = floor (sqrt n')
    in  if (candidate * candidate == n)
        then Just candidate
        else Nothing

-- =====

-- Is a character whitespace? (SV 3.1a LRM A.9.4)
-- (Note that Verilog 2001 LRM section 2.2 -- but not its grammar -- also has \f)

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace '\t' = True
isWhitespace '\n' = True
isWhitespace '\f' = True
isWhitespace '\r' = True
isWhitespace _ = False


-- =========================
-- A computational simple hash
-- 4000000063 and 1442968193 are large primes that fit in 32 bits

data Hash = Hash !Word32 !Word32

hashInit :: Hash
hashInit = Hash 0 4000000063

-- showpair (x,y) = "(" ++ (showHex x ("," ++ (showHex y ")")))

nextHash :: Hash -> [Word8] -> Hash
nextHash h s = foldl' f h s
    where f :: Hash -> Word8 -> Hash
          f (Hash x y) c =
              let y' = (rotate x 5) + (toEnum (fromEnum c))
                  x' = y + y' + 1442968193
              in Hash x' y'

nextHash32 :: Hash -> Word32 -> Hash
nextHash32 (Hash x y) n =
    let y' = (rotate x 20) + n
        x' = y + y' + 1442968193
    in Hash x' y'

nextHash64 :: Hash -> Word64 -> Hash
nextHash64 h n =
    let (hi,lo) = n `quotRem` (2^(32::Int))
    in nextHash32 (nextHash32 h (fromIntegral lo)) (fromIntegral hi)

hashValue :: Hash -> Word64
hashValue (Hash x y) = ((fromIntegral x) `shiftL` 32) .|. (fromIntegral y)

showHash :: Hash -> String
showHash h = show (hashValue h)
