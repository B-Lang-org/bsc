
module Main(main) where
-- Haskell libs

import CuddBdd
import Foreign
import System

main :: IO ()
main =  do
        putStr "Hello World\n" 
        args <- getArgs   
        let 
            size :: Int 
            size = read (args!!0) 

        CuddBdd.tester 
        queenTester size         

queenTester :: Int -> IO () 
queenTester size = do
        mgr <- newBddMgrFull False 0 0 256 262144 0

        queens <- genBoard mgr size
        putStr "Valid board positions\n"
        bddPrintMinterms queens
        putStr $ "For n Queens (n=" ++ (show size) ++ ") Number of solutions is "  
        soln <- bddCountMinterms queens (size*size)
        putStrLn (show soln)
        putStr "Good Bye World\n" 
        touchForeignPtr mgr 



type SState = (BddMgr,Int)
type Pos    = (Int,Int)

toIndex :: Int -> Int -> Int -> Int 
toIndex s i j = (s*(i-1)) + (j-1)

-- Returns the bdd variable with
var :: SState -> Pos -> IO Bdd
var (m,size) (i,j) = bddGetVar m (toIndex size i j )

notVar :: SState -> Pos -> IO Bdd 
notVar (m,size) (i,j) = bddGetVar m (toIndex size i j ) >>= bddNot



--checkCol n i j = var i j `implies` bddAnds [ notVar k j | k <- [1..n], k /= i ]
checkCol :: Int -> Pos -> [Pos]
checkCol n (i,j) = [(k,j) | k <- [1..n] , k /= i ]

-- checkRow n i j = var i j `implies` bddAnds [ notVar i l | l <- [1..n], l /= j ]
checkRow :: Int -> Pos -> [Pos]
checkRow n (i,j) =   [(i,l) | l <- [1..n] , l /=j ] -- [(i,j)]


--checkDiagL n i j = var i j `implies` bddAnds [ notVar k m | k <- [1..n], let m = j+k-i, 1 <= m && m <= n, k /= i ]
checkDiagL :: Int -> Pos -> [Pos] 
checkDiagL n (i,j) = [(k,m) | k <- [1..n] , let m = j+k-i, 1 <= m && m <= n, k /= i ]

--checkDiagR n i j = var i j `implies` bddAnds [ notVar k m | k <- [1..n], let m = j+i-k, 1 <= m && m <= n, k /= i ]
checkDiagR :: Int -> Pos -> [Pos]
checkDiagR n (i,j) = [(k,m)  | k <- [1..n], let m = j+i-k, 1 <= m && m <= n, k /= i]


-- Builds BDD which is the implication of Pos -> NOT (poss) 
positionCheck :: SState -> (Pos,[Pos]) -> IO Bdd
positionCheck (m,n) ((i,j), poss) =
              do
                v1 <- mapM (notVar (m,n)) poss  -- [Bdd]
                t1 <- bddAndList m v1  -- Bdd
                t2 <- var (m,n) (i,j)  -- Bdd
                bddImplies t2 t1    -- IO Bdd



-- make sure there is (at least) one queen on each row
-- bddAnds [ bddOrs [ bddVar (V i j) | j <- [1..n] ] | i <- [1..n] ]
validBoard :: SState -> IO Bdd 
validBoard (m,n) =
           let
            varsInRow i = [(i,j) | j <- [1..n]]  -- Int -> [(Int,Int)]
            oneRow i =  mapM (var (m,n)) (varsInRow i) -- Int -> [ IO^H^H Bdd]
           in do
              t1 <- mapM oneRow [1..n]    -- [[Bdd]]
              t2 <- mapM (bddOrList m) t1 -- [Bdd]
              bddAndList m t2


-- generates a BDD describing the legal positions to solve the n Queens problem
-- alternately,  generate (BddMgr, Bdd) pair a output.
genBoard :: BddMgr -> Int -> IO Bdd
genBoard mgr size =
         let
            board = [(i,j) | i<-[1..size], j<-[1..size] ]
            rp = zip board (map (checkRow size) board)  ++ 
                 zip board (map (checkCol size) board)  ++ 
                 zip board (map (checkDiagR size) board)  ++ 
                 zip board (map (checkDiagL size) board)   -- [(Pos, [Pos]) ]
            
         in do
            validImpl <- mapM (positionCheck (mgr,size)) rp -- [Bdd]
            t1 <- bddAndList mgr validImpl 

            b <- validBoard (mgr,size)

            bddAndList mgr [t1, b]
         
{-

-- Some BDD test code to compute the solution to the N queen problem.
-- Lennart's code

data V = V Int Int
	deriving (Eq, Ord)

instance Show V where
	show (V i j) = "v" ++ show i ++ "_" ++ show j

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
