module BoolOpt(optBoolExprQM) where

import Data.List(union, sort, nub, (\\))

import ErrorUtil
import BoolExp(BoolExp(..))

-- import Debug.Trace


getVars :: (Eq a) => BoolExp a -> [a]
getVars (And e1 e2) = getVars e1 `union` getVars e2
getVars (Or e1 e2) = getVars e1 `union` getVars e2
getVars (Not e1) = getVars e1
getVars (If e1 e2 e3) = getVars e1 `union` getVars e2 `union` getVars e3
getVars (Var a) = [a]
getVars TT = []
getVars FF = []

eval :: (Eq a) => [(a, Bool)] -> BoolExp a -> Bool
eval r (And e1 e2) = eval r e1 && eval r e2
eval r (Or e1 e2) = eval r e1 || eval r e2
eval r (Not e1) = not (eval r e1)
eval r (If e1 e2 e3) = if eval r e1 then eval r e2 else eval r e3
eval r (Var v) = case lookup v r of Just b -> b; Nothing -> internalError ("BoolOpt.eval ")
eval r TT = True
eval r FF = False

mkAnd :: [BoolExp a] -> BoolExp a
mkAnd [] = TT
mkAnd [x] = x
mkAnd (x:xs) = x `And` mkAnd xs

mkOr :: [BoolExp a] -> BoolExp a
mkOr [] = FF
mkOr [x] = x
mkOr (x:xs) = x `Or` mkOr xs

data Bool3 = F | T | U
        deriving (Eq, Ord, Show)

to3 :: Bool -> Bool3
to3 True = T
to3 False = F

adjacent :: [Bool3] -> [Bool3] -> Bool
adjacent xs ys = length (filter id (zipWith (/=) xs ys)) == 1

joinB :: [Bool3] -> [Bool3] -> [Bool3]
joinB xs ys = zipWith f xs ys
  where f x y = if x == y then x else U

covers :: [Bool3] -> [Bool3] -> Bool
covers xs ys = and (zipWith f xs ys)
  where f U _ = True
        f T T = True
        f F F = True
        f _ _ = False

genEnvs :: [a] -> [[(a, Bool)]]
genEnvs [] = [[]]
genEnvs (x:xs) =
        let r = genEnvs xs
        in  map ((x, False):) r ++ map ((x, True):) r


-- Minimize a boolean function with Quine-McClusky
-- Give up if too many variables.
optBoolExprQM :: Ord a => Int -> BoolExp a -> Maybe (BoolExp a)
optBoolExprQM n e =
        let vs = sort (getVars e)
            nvs = length vs
            rs = genEnvs vs
            rows = map (map (to3 . snd)) (filter (`eval` e) rs)
            grps = filter (not . null) (map (\ n -> filter (\ row -> length (filter (==T) row) == n) rows) [0..nvs])

            loop all marked [] = all \\ marked
            loop all marked grps =
                let (grps', us) = unzip (sweep step grps)
                in  loop (concat grps' ++ all) (nub (concat us) ++ marked) (filter (not . null) grps')

            prime = loop (concat grps) [] grps                -- prime implicants

            selPrimes sel cprime [] = sel
            selPrimes sel [] _ = internalError "selPrimes"
            selPrimes sel cprime@(cp:_) crows =
                let allCovers = [ (r, filter (flip covers r) cprime) | r <- crows ]
                    isSingle p = [p] `elem` map snd allCovers
                    -- select prime implicants that is the sole cover of a term
                    sprime = filter isSingle cprime
                    nprime = if null sprime then [cp] else sprime
                in  --trace ("nprime " ++ show nprime ++ "\n")
                    selPrimes (nprime ++ sel) (cprime \\ nprime) [ r | r <- crows, all (\ p -> not (covers p r)) nprime ]

            ps = selPrimes [] prime rows

            e' = mkOr (map (\ row -> mkAnd (f row vs)) ps)
                          where f (U:rs) (_:vs) = f rs vs
                                f (T:rs) (v:vs) = Var v : f rs vs
                                f (F:rs) (v:vs) = Not (Var v) : f rs vs
                                f [] [] = []
                                f _ _ = internalError
                                        ("BoolOpt.optBoolExprQM.e'")

        in  if nvs > n then
                --trace ("optBoolExprQM " ++ show nvs)
                Nothing
            else
                Just e'

step :: [[Bool3]] -> [[Bool3]] -> ([[Bool3]], [[Bool3]])
step xs ys =
        let (ps, qss) = unzip [ (joinB x y, [x,y]) | x <- xs, y <- ys, adjacent x y]
        in  (nub ps, nub (concat qss))

sweep :: (a -> a -> b) -> [a] -> [b]
sweep f (x:xs@(y:_)) = f x y : sweep f xs
sweep _ _ = []
