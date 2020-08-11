{-# LANGUAGE CPP #-}
module BDD(
        BDD, bddFalse, bddTrue, bddVar,
        bddAnd, bddOr, bddNot, bddImplies, bddEquiv,
        bddRestrict, bddAllSat,
        bddIsTrue, bddIsFalse, bddIsIf) where

import Control.Monad(liftM, ap)

import Data.List(sort)
import qualified Data.Map as M
import qualified Data.IntMap as I


type Unique = Int
--type UniquePair = (Int, Int)
type UniquePair = Int
mkPair :: Unique -> Unique -> UniquePair
--mkPair x y = (x, y)
mkPair x y = x * 65536 + y

data BDD a = N !Unique a (BDD a) (BDD a) | L !Bool
        deriving (Show)

bddFalse, bddTrue :: BDD a
bddFalse = L False
bddTrue  = L True

bddAnd, bddOr :: Ord a => BDD a -> BDD a -> BDD a
bddAnd a b = apply (&&) a b
bddOr  a b = apply (||) a b

bddNot :: BDD a -> BDD a
--bddNot e = bddOp (\ x y -> not x) e bddFalse                -- inefficient
bddNot e = fst (flip I.empty e)
  where flip m (L b) = (L (not b), m)
        flip m (N u x t f) =
            case I.lookup u m of
            Just b -> (b, m)
            Nothing ->
                case flip m t of
                (t', m') ->
                    case flip m' f of
                    (f', m'') ->
                        let n' = N u x t' f'
                        in  (n', I.insert u n' m'')

bddImplies, bddEquiv :: (Ord a) => BDD a -> BDD a -> BDD a
bddImplies a b = apply (\ x y -> not x || y) a b
bddEquiv a b = apply (==) a b

bddVar :: a -> BDD a
bddVar v = N 0 v bddFalse bddTrue

--bddOp :: (Ord a) => (Bool -> Bool -> Bool) -> BDD a -> BDD a -> BDD a
--bddOp op e1 e2 = run $ app op e1 e2

-- Check
bddIsTrue :: BDD a -> Bool
bddIsTrue (L b) = b
bddIsTrue _ = False

bddIsFalse :: BDD a -> Bool
bddIsFalse (L b) = not b
bddIsFalse _ = False

bddIsIf :: BDD a -> Maybe (a, BDD a, BDD a)
bddIsIf (L _) = Nothing
bddIsIf (N _ v f t) = Just (v, t, f)

bddAllSat :: BDD a -> [[(a, Bool)]]
bddAllSat (L True) = [ [] ]
bddAllSat (L False) = []
bddAllSat (N _ v l r) = map ((v,False):) (bddAllSat l) ++ map ((v,True):) (bddAllSat r)

bddRestrict :: (Ord a) => [(a, Bool)] -> BDD a -> BDD a
bddRestrict vs b = run $ restrict (sort vs) b

-- bddSubstitute
-- bddIsIso

----

nodeNo :: BDD a -> Unique

nodeNo (L False) = 0
nodeNo (L True)  = 1
nodeNo (N u _ _ _) = u

----

-- The state contains 3 parts:
--   the next unique number to use
--   a cache of N nodes to avoid recreating an existing N node
data S a = S !Unique (M.Map (UniquePair, a) (BDD a))

newtype M v a = M (S v -> (S v, a))

instance Monad (M v) where
    return a = M $ \ s -> (s, a)
    M a >>= f = M $ \ s ->
        case a s of
        (s', b) ->
            let M f' = f b
            in  f' s'

instance Functor (M v) where
  fmap = liftM

instance Applicative (M v) where
  pure = return
  (<*>) = ap

run :: M v a -> a
run (M m) =
    case m (S 2 M.empty) of
    (_, a) -> a

genSym :: M a Unique
genSym = M $ \ (S u h) -> (S (u+1) h, u)

find :: (Ord a) => a -> BDD a -> BDD a -> M a (Maybe (BDD a))
find v b1 b2 = M $ \ s@(S _ h) -> (s, M.lookup (mkPair (nodeNo b1) (nodeNo b2), v) h)

insert :: (Ord a) => a -> BDD a -> BDD a -> BDD a -> M a ()
insert v b1 b2 n = M $ \ s@(S u h) -> (S u (M.insert (mkPair (nodeNo b1) (nodeNo b2), v) n h), ())

----

apply :: (Ord a) => (Bool -> Bool -> Bool) -> BDD a -> BDD a -> BDD a
apply op e1 e2 = run $ app op e1 e2

-- XXX should pre-compute what to do when constants are encountered
app :: (Ord a) => (Bool -> Bool -> Bool) -> BDD a -> BDD a -> M a (BDD a)
app op e1 e2 = doApp op e1 e2

doApp :: (Ord a) => (Bool -> Bool -> Bool) -> BDD a -> BDD a -> M a (BDD a)
doApp op (L b1) (L b2) = return (L (op b1 b2))
doApp op e@(L b) (N _ v f t) = do
    f' <- doApp op e f
    t' <- doApp op e t
    node v f' t'
doApp op (N _ v f t) e@(L b) = do
    f' <- doApp op f e
    t' <- doApp op t e
    node v f' t'
doApp op e1@(N _ v1 f1 t1) e2@(N _ v2 f2 t2) =
    case v1 `compare` v2 of
    LT -> do
        f' <- doApp op f1 e2
        t' <- doApp op t1 e2
        node v1 f' t'
    EQ -> do
        f' <- doApp op f1 f2
        t' <- doApp op t1 t2
        node v1 f' t'
    GT -> do
        f' <- doApp op e1 f2
        t' <- doApp op e1 t2
        node v2 f' t'

node :: (Ord a) => a -> BDD a -> BDD a -> M a (BDD a)
node v a b =
    if nodeNo a == nodeNo b then
        return a
    else do
        mv <- find v a b
        case mv of
         Just n -> return n
         Nothing -> do
            u <- genSym
            let n = N u v a b
            insert v a b n
            return n

restrict :: (Ord a) => [(a, Bool)] -> BDD a -> M a (BDD a)
restrict [] b = return b
restrict vs b@(L _) = return b
restrict ((v,c):vs) b@(N _ v' f t) =
    case v `compare` v' of
    LT -> restrict vs b
    EQ -> if c then restrict vs t else restrict vs f
    GT -> do
        -- XXX exponential
        f' <- restrict vs f
        t' <- restrict vs t
        node v' f' t'

{-

-- Some BDD test code to compute the solution to the N queen problem.

data V = V Int Int
        deriving (Eq, Ord)

instance Show V where
        show (V i j) = "v" ++ itos i ++ "_" ++ itos j

queens :: Int -> [[V]]
queens = map (map fst . filter snd) . bddAllSat . genBoard

genBoard :: Int -> BDD V
genBoard n =
    bddAnds
      [
        checkRow n i j `bddAnd`
        checkCol n i j `bddAnd`
        checkDiagL n i j `bddAnd`
        checkDiagR n i j
      | i <- [1..n], j <- [1..n]
      ]
  `bddAnd`
    -- make sure there is (at least) one queen on each row
    bddAnds [ bddOrs [ bddVar (V i j) | j <- [1..n] ] | i <- [1..n] ]

checkRow n i j = var i j `implies` bddAnds [ notVar i l | l <- [1..n], l /= j ]
checkCol n i j = var i j `implies` bddAnds [ notVar k j | k <- [1..n], k /= i ]
checkDiagL n i j = var i j `implies` bddAnds [ notVar k m | k <- [1..n], let m = j+k-i, 1 <= m && m <= n, k /= i ]
checkDiagR n i j = var i j `implies` bddAnds [ notVar k m | k <- [1..n], let m = j+i-k, 1 <= m && m <= n, k /= i ]

implies x y = bddNot x `bddOr` y

notVar i j = bddNot (var i j)

var i j = bddVar (V i j)

bddAnds xs = foldr bddAnd bddTrue  xs
bddOrs  xs = foldr bddOr  bddFalse xs

main = print (queens 5)

-}
