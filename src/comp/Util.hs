{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Util where

import Data.Char(intToDigit, isAlpha, isAlphaNum)
import Data.Word(Word32,Word64)
import Data.Bits
import Data.List(sort, sortBy, group, groupBy, nubBy, union, partition, intersperse, foldl')
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

-- note that trace, traces, traceM sometimes do not work correctly
-- when compiled with -O2 (e.g., in tiExpl''')
traces :: String -> a -> a
traces s x = if s==s then trace s x else internalError "Util.traces"
tracep p s x = if p then traces s x else x

traceM :: (Monad m) => String -> m ()
traceM s = do msg <- return s
              trace msg $ return ()

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

dbgTrace level s a = if (dbgLevel >= level) then (trace s a) else a
dbgTraceM level s = if (dbgLevel >= level) then (traceM s) else return ()


-- =====
-- Internal compiler assertions

assert True msg v = v
assert False msg v = internalError ("assertion failed: "++msg)


-- =====
-- String utilities

quote :: String -> String
quote s = "`" ++ s ++ "'"

doubleQuote :: String -> String
doubleQuote s = "\"" ++ s ++ "\""


unwordsAnd = unwordsx "and"
unwordsOr = unwordsx "or"

unwordsx _ [] = ""
unwordsx _ [x] = x
unwordsx s [x1, x2] = unwords [x1, s, x2]
unwordsx s xs = unwordsWith ", " (init xs++[s++" "++last xs])

unwordsWith d [] = ""
unwordsWith d [x] = x
unwordsWith d (x:xs) = x++d++unwordsWith d xs

-- This function is in Data.List as of GHC 6.8
-- At some point in the future, this version can be removed.
intercalate :: [a] -> [[a]] -> [a]
intercalate xs xss = concat (intersperse xs xss)

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
        '"' -> "\\\""	-- backslash double-quote
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


rTake n = reverse . take n . reverse
rDrop n = reverse . drop n . reverse

unions l = foldr union [] l

concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f as = do
  temp <- mapM f as
  return (concat temp)

-- Haskell Prelude definition says that this is the same as "any (eq x)"
elemBy			:: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy eq _ []		= False
elemBy eq x (y:ys)	= eq x y || elemBy eq x ys

-- changed so that the lookup info need not be the same type
lookupBy                :: (c -> a -> Bool) -> c -> [(a,b)] -> Maybe b
lookupBy eq _ []        =  Nothing
lookupBy eq key ((x,y):xys)
    | (key `eq` x)      =  Just y
    | otherwise         =  lookupBy eq key xys

splitBy :: [a->Bool] -> [a] -> [[a]]
splitBy [] _  = []
splitBy _  [] = []
splitBy (p:ps) xs = let (xs', xs'') = span p xs in xs' : splitBy ps xs''

-- splits a list into a list of list where length is each sub list is n
splitBySize :: Int -> [a] -> [[a]]
splitBySize n [] = [[]]
splitBySize n ls = [s1] ++ (splitBySize n s2)
            where
             (s1,s2) = splitAt n ls

findSame :: (Ord a) => [a] -> [[a]]
findSame = filter ((>1) . length) . group . sort

findSameLe :: (a->a->Bool) -> [a] -> [[a]]
findSameLe le = filter ((>1) . length) . groupBy eq . sortLe le
        where eq x y = le x y && le y x		-- inefficient

-- this is awfully slow!
findSameEq :: (a->a->Bool) -> [a] -> [[a]]
findSameEq eq [] = []
findSameEq eq (x:xs) =
        case partition (eq x) xs of
            ([], ns) -> findSameEq eq ns
            (es, ns) -> (x:es) : findSameEq eq ns

findSameBy :: (a -> a -> Ordering) -> (a -> a -> Bool) -> [a] -> [[a]]
findSameBy sortFn groupFn =
    filter ((>1) . length) . (groupBy groupFn) . (sortBy sortFn)


toMaybe :: Bool -> a -> Maybe a
toMaybe False _ = Nothing
toMaybe True a = Just a

-- how does this differ from "breakAt" in Libs/ListUtil.hs ?
breakAt x xs =
        case span (/= x) xs of
            (ys,_:zs) -> (ys,zs)
            p -> p

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

mergeManyWithCmp :: (a -> a -> Ordering) -> (a -> a -> a) -> [[a]] -> [a]
mergeManyWithCmp _   _ [] = []
mergeManyWithCmp _   _ [xs] = xs
mergeManyWithCmp cmp f xss = foldl1 (mergeWithCmp cmp f) xss

subsets []     = [[]]
subsets (x:xs) = map (x:) ss ++ ss
    where ss = subsets xs

updList :: [a] -> Integer -> a -> [a]
updList (_:xs) 0 y = y : xs
updList (x:xs) n y = x : updList xs (n-1) y
updList _ _ _ = internalError ("updList")

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
fst2of4 (x,y,_,_) = (x,y)

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

unzipWith2 :: (a -> b -> (c, d)) -> [a] -> [b] -> ([c], [d])
unzipWith2 f l1 l2 = unzip (zipWith f l1 l2)

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

--mapFst f xys = [(f x, y) | (x,y)<-xys]

--mapSnd f xys = [(x, f y) | (x,y)<-xys]

mapThd f xyzs = [(x, y, f z) | (x, y, z) <- xyzs]

joinByFst :: (Ord a) => [(a, b)] -> [(a, [b])]
joinByFst =
    map (\ xys@((x,_):_) -> (x, map snd xys)) .
    groupBy (\ (x,_) (y,_) -> x==y) .
    sortBy (\ (x,_) (y,_) -> x `compare` y)

joinByFstLe :: (a->a->Bool) -> [(a, b)] -> [(a, [b])]
joinByFstLe le =
    map (\ xys@((x,_):_) -> (x, map snd xys)) .
    groupBy (\ (x,_) (y,_) -> not (le x y)) .
    sortLe (\ (x,_) (y,_) -> le x y)

-- This has different type from "assoc" in Libs/ListUtil.hs
assoc :: (Eq a) => [(a,b)] -> a -> b
assoc xys x =
    case lookup x xys of
    Just y -> y
    Nothing -> internalError "assoc"

sortFst xs = sortBy (\(x,_) (y,_) -> x `compare` y) xs

mergeWith :: (Ord b) => (a -> a -> a) -> [(b, a)] -> [(b, a)] -> [(b, a)]
mergeWith f = mergeWithCmp cmpFst f'
    where f' (k,v) (_,v') = (k, v `f` v')

commonElts :: (a -> b -> Ordering) -> [a] -> [b] -> [(a, b)]
commonElts _   [] _ = []
commonElts _   _ [] = []
commonElts cmp xxs@(x:xs) yys@(y:ys) =
    case x `cmp` y of
    EQ -> (x,y) : commonElts cmp xs ys
    LT -> commonElts cmp xs yys
    GT -> commonElts cmp xxs ys

mergeManyWith :: (Ord b) => (a -> a -> a) -> [[(b, a)]] -> [(b, a)]
mergeManyWith _ [] = []
mergeManyWith _ [xs] = xs
mergeManyWith f xss = foldl1 (mergeWith f) xss

flattenPairs :: [(a,a)] -> [a]
flattenPairs [] = []
flattenPairs ((x,y):xys) = x:y:flattenPairs xys

makePairs :: [a] -> [(a,a)]
makePairs [] = []
makePairs (x:y:xs) = (x, y) : makePairs xs
makePairs _ = internalError "Util.makePairs: failed"

-- all pairs except pairs of an item with itself
allPairs [] = []
allPairs (x:xs) = concat [[(x,x'), (x',x)] | x' <- xs] ++ allPairs xs

-- all unique pairs -- i.e. only one of (x,y) and (y,x)
uniquePairs [] = []
uniquePairs (x:ys) = [(x,y) | y <- ys] ++ uniquePairs ys

-- all pairs of an item with itself
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

nubByFst :: (Eq a) => [(a,b)] -> [(a,b)]
nubByFst xs = nubBy f xs
  where f a b = (fst a == fst b)

-- Monad utilities
anyM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
anyM f = foldM comb False
  where comb any elt = if any then
                         return any
                       else f elt

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f l = partitionM' f l ([],[])
partitionM' f [] acc = return acc
partitionM' f (x:xs) (ts, fs) = do
  b <- f x
  if b then partitionM' f xs (x:ts, fs)
   else partitionM' f xs (ts, x:fs)

sortM :: (Monad m) => (a -> a -> m Ordering) -> [a] -> m [a]
sortM cmp [] = return []
sortM cmp (x:xs) = do
  let cmp' y = cmp y x >>= (return . (== LT))
  (ls, hs) <- partitionM cmp' xs
  ls' <- sortM cmp ls
  hs' <- sortM cmp hs
  return (ls' ++ [x] ++ hs')

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

-- XXX: isn't this just Control.Monad(msum)
firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (j@(Just _):_) = j
firstJust (_:ms) = firstJust ms

fromJustOrErr :: String -> Maybe value -> value
fromJustOrErr err Nothing  = internalError err
fromJustOrErr _   (Just v) = v


-- =====
-- Tuple utilities

pair x y = (x, y)

swap (x,y) = (y,x)

apFst f (x, y) = (f x, y)

apSnd f (x, y) = (x, f y)

fst3 (x,_,_) = x
snd3 (_,x,_) = x
thd  (_,_,x) = x
fst2of3 (x,y,_) = (x,y)
lst2of3 (_,y,z) = (y,z)

fst4 (x,_,_,_) = x
snd4 (_,x,_,_) = x
thd4 (_,_,x,_) = x
fth4 (_,_,_,x) = x
fst3of4 (x,y,z,_) = (x,y,z)

fst4of5 (a,b,c,d,_) = (a,b,c,d)
fifth5 (_,_,_,_,x) = x

ordPair (x,y) = if x < y then (x,y) else (y,x)

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

unJust (Just x) = x
unJust Nothing = internalError "Util.unJust: failed"

-- XXX: isn't this just Data.Maybe(fromMaybe)
mDefault s Nothing = s
mDefault s (Just x) = x

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
-- Function utilities

fix :: (Eq a) => (a->a) -> a -> a
fix f x =
    let x' = f x
    in  if x == x' then x else fix f x'


-- =====

-- Verilog naming utilities
-- one more valid characters
isValidVerilogName :: String -> Bool
isValidVerilogName str = (not $ null str) && headok && tailok
    where headok = isAlpha (head str) || (head str) == '_'
          tailok = any validChar (tail str)
          validChar c = isAlphaNum c || (c == '_') || (c == '$')

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

nextHash :: Hash -> String -> Hash
nextHash h s = foldl' f h s
    where f :: Hash -> Char -> Hash
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

hashValue32 :: Hash -> Word32
hashValue32 (Hash x y) = x `xor` y

showHash :: Hash -> String
showHash h = show (hashValue h)
