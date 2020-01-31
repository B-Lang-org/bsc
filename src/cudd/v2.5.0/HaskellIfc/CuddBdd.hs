{-# LANGUAGE ForeignFunctionInterface, CPP #-}
{-# OPTIONS_GHC -fwarn-name-shadowing -fwarn-missing-signatures  #-}
-- above line sets compiler options -- needed for portability.

module CuddBdd (
    tester,
    BddMgr,
    Bdd,
    BddModel,
    BddStat,
    newBddMgr,
    newBddMgrFull,
    bddNewVar,
    bddNewVarAtLevel,
    bddGetVar,
    bddGetLevel,
    bddGetIndex,
    bddTrue,
    bddFalse,
    bddTrueFalse,
    bddIte,
    bddAnd,
    bddNor,
    bddNand,
    bddOr,
    bddXor,
    bddXnor,
    bddNot,
    bddIntersect,
    bddImplies,
    bddAndList,
    bddOrList,
    bddXorList,
    bddConstVector,
    bddEQVector,
    bddULEVector,
    bddULTVector,
    bddSLEVector,
    bddSLTVector,
    bddSubVector,
    bddAddVector,
    bddIteVector,
    bddIsTrue,
    bddIsFalse,
    bddIsComplement,
    bddIsConst,
    bddBiImplication,
    bddGetModel,
    bddPrintMinterms,
    bddCountMinterms,
    bddSupportSize,
    bddDagRatio,
    bddDagSize,
    bddStats,
    nullBddMgr,
    showBdd,
    showBddList,
    bddVarCount,
    dotDump
    )where

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 707)
import Foreign.ForeignPtr
import Foreign.ForeignPtr.Unsafe(unsafeForeignPtrToPtr)
#elif (__GLASGOW_HASKELL__ >= 702)
import Foreign.ForeignPtr hiding (unsafeForeignPtrToPtr)
import Foreign.ForeignPtr.Unsafe(unsafeForeignPtrToPtr)
#else
import Foreign.ForeignPtr
#endif

import Foreign.Ptr
import Foreign.Marshal
import Foreign.C.Types

import Control.Monad
import Data.List(intersperse)
import Text.Printf(printf)
import System.IO(stdout, hFlush)

-- Create specific types for the pointers to the C-level data structures.
data XBddP = XBddP                      -- corresponds to WBddNode in C
data XBddM = XBddM                      -- corresponds to DdManager in C

type XBddMgr = Ptr XBddM                -- Aliases for haskell pointer to these C types
type XBddPtr = Ptr XBddP

data RawBdd = RawBdd                    -- a DdNode Pointer from C --  All these should have reference count > 1
type RawBddPtr = Ptr RawBdd             --


-- These two types are public to this package, and represent the manager, and the bdd
type BddMgr = ForeignPtr XBddM
type Bdd = ForeignPtr XBddP

-- Defines a model of the Bdd for external processing
data BddModel = BddNode BddId Bool Bdd Bdd |
                BddLeaf !Bool

-- Defines a model of the Bdd for internal processing
data BddModelInternal = IBddNode BddId Bool RawBddPtr RawBddPtr |
                        IBddLeaf !Bool

-- this may change if the package type is changed or other internals
type BddId = CInt

-- a type used to show statistics about a give bdd.
data BddStat = BddStat { support ::Int
                       ,dagsize::Int
                       ,ratio::Double}

instance Show BddStat where
    show bs =  "("++ show (support bs) ++ "," ++ show (dagsize bs) ++ "," ++ (printf "%.2g" (ratio bs)) ++ ")"

-- Used for printing
data PrintExpr = Const0 |
                 Const1 |
                 Prod String |
                 Sum  String |
                 Term String

instance Show PrintExpr where
         show Const0 = "False"
         show Const1 = "True"
         show (Prod e) =  e
         show (Sum e)  =  e
         show (Term e) =  e


-- cast functions
castI :: (Integral a, Integral b) => a -> b
castI = fromIntegral

castD :: (RealFloat a, RealFloat b) => a -> b
castD = (uncurry encodeFloat) . decodeFloat

-- the following are functions which must be imported from the cudd package.

-- Functions dealing with the creation and desturction of the bdd manager
foreign import ccall hcuddInit :: CInt -> CUInt -> CUInt -> CUInt -> CUInt -> CULong -> IO XBddMgr
foreign import ccall hcuddDestroyBdd :: XBddPtr -> IO ()
foreign import ccall hcuddNull :: IO XBddMgr

#if __GLASGOW_HASKELL__ &&  __GLASGOW_HASKELL__ < 600
foreign import ccall "cudd_interface.h"
                                  hcuddQuit :: XBddMgr -> IO ()
foreign import ccall "cudd_interface.h"
                                  hcuddnoop :: XBddMgr -> IO ()
#endif

foreign import ccall hcuddVarCount :: XBddMgr -> CInt

-- Functions dealing with the creation or access of variables. --------------------------------------------------
foreign import ccall hcuddBddNewVar  :: XBddMgr -> IO XBddPtr
foreign import ccall hcuddBddNewVarAtLevel :: XBddMgr -> CInt -> IO XBddPtr
foreign import ccall hcuddBddIthVar :: XBddMgr -> CInt -> IO XBddPtr
foreign import ccall hcuddGetLevel :: XBddMgr -> CInt -> IO CInt

foreign import ccall hcuddReadOne :: XBddMgr ->  IO XBddPtr

foreign import ccall hcuddReadOneRaw :: XBddMgr -> IO RawBddPtr

foreign import ccall hcuddReadZeroRaw :: XBddMgr -> IO RawBddPtr

foreign import ccall hcuddReadZero :: XBddMgr -> IO XBddPtr



-- Functions for basic logic manipulations --------------------------------------------------------------
foreign import ccall hcuddBddIte :: XBddPtr -> XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddAnd :: XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddOr  :: XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddXor :: XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddNand :: XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddNor ::  XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddXNor :: XBddPtr -> XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddNot :: XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddIntersect ::  XBddPtr -> XBddPtr -> IO XBddPtr

foreign import ccall "hcuddIsTrue" hcuddIsTrueI ::  XBddPtr -> IO CInt
hcuddIsTrue :: XBddPtr -> IO Bool
hcuddIsTrue p = hcuddIsTrueI p >>= return . toBool

foreign import ccall "hcuddIsFalse" hcuddIsFalseI ::  XBddPtr -> IO CInt
hcuddIsFalse :: XBddPtr -> IO Bool
hcuddIsFalse p = hcuddIsFalseI p >>= return . toBool

foreign import ccall "hcuddLeq" hcuddLeqI ::  XBddPtr -> XBddPtr -> IO CInt

hcuddLeq ::  XBddPtr -> XBddPtr -> IO Bool
hcuddLeq a b = hcuddLeqI a b >>= return . toBool

-- Functions for debugging
foreign import ccall hcuddPrintMinterm ::  XBddPtr -> IO CInt
foreign import ccall hcuddCountMinterm ::  XBddPtr -> CInt -> IO CDouble
foreign import ccall hcuddDotDump ::  XBddPtr  -> IO ()


-- Utility functions for memory management -------------------------------------------------------
foreign import ccall "&hcuddManagerDestructor" hcuddManagerDestructor :: FunPtr ( XBddMgr -> IO () )
foreign import ccall "&hcuddNoOpDestructor"    hcuddNoOpDestructor :: FunPtr ( XBddMgr -> IO () )

foreign import ccall "&hcuddBddDestructor"     hcuddBddDestructor :: FunPtr ( XBddPtr -> IO () )
foreign import ccall                           hcuddRef :: RawBddPtr ->  IO ()


-- Utility function for accessing and querying node -- TODO these can possibly become unwrapped
foreign import ccall hcuddSupportSize :: XBddPtr -> IO CInt
foreign import ccall hcuddDagRatio :: XBddPtr -> IO CDouble
foreign import ccall hcuddDagSize :: XBddPtr -> IO CInt

foreign import ccall hcuddNodeReadIndex :: XBddPtr -> IO CInt
foreign import ccall hcuddBddThen :: XBddPtr -> IO XBddPtr
foreign import ccall hcuddBddElse :: XBddPtr -> IO XBddPtr

foreign import ccall "hcuddNodeReadIndexRaw" hcuddNodeReadIndexRawUnsafe :: RawBddPtr -> CInt
foreign import ccall hcuddBddThenRawUnsafe :: RawBddPtr -> RawBddPtr
foreign import ccall hcuddBddElseRawUnsafe :: RawBddPtr -> RawBddPtr


foreign import ccall "hcuddIsComplement" hcuddIsComplementI :: XBddPtr -> IO CInt
hcuddIsComplement :: XBddPtr -> IO Bool
hcuddIsComplement a = hcuddIsComplementI a >>= return . toBool

foreign import ccall "hcuddIsConstant" hcuddIsConstantI :: XBddPtr -> IO CInt
hcuddIsConstant :: XBddPtr -> IO Bool
hcuddIsConstant a = hcuddIsConstantI a >>= return . toBool

foreign import ccall "hcuddIsNull" hcuddIsNullI :: XBddPtr -> IO CInt
hcuddIsNull :: XBddPtr -> IO Bool
hcuddIsNull a = hcuddIsNullI a >>= return . toBool

foreign import ccall "hcuddIsComplementRaw" hcuddIsComplementRawI :: RawBddPtr -> CInt
hcuddIsComplementRaw :: RawBddPtr -> Bool
hcuddIsComplementRaw  = toBool . hcuddIsComplementRawI

foreign import ccall "hcuddIsConstantRaw" hcuddIsConstantRawI :: RawBddPtr -> CInt
hcuddIsConstantRaw :: RawBddPtr -> Bool
hcuddIsConstantRaw = toBool . hcuddIsConstantRawI



foreign import ccall hcuddGetRawUnsafe :: XBddPtr -> RawBddPtr
foreign import ccall hcuddToXBddPtr :: XBddMgr -> RawBddPtr -> IO XBddPtr

foreign import ccall hcuddRawAnd :: RawBddPtr -> XBddPtr -> IO RawBddPtr
foreign import ccall hcuddRawOr  :: RawBddPtr -> XBddPtr -> IO RawBddPtr
foreign import ccall hcuddRawXor :: RawBddPtr -> XBddPtr -> IO RawBddPtr

foreign import ccall hcuddRawULEBit :: RawBddPtr -> XBddPtr -> XBddPtr -> IO RawBddPtr
foreign import ccall hcuddRawAddBit :: CInt -> RawBddPtr -> XBddPtr -> XBddPtr -> IO RawBddPtr
foreign import ccall hcuddRawCoutBit :: CInt -> RawBddPtr -> XBddPtr -> XBddPtr -> IO RawBddPtr


-- We may want to add a type argument here, since we can have bdd of different variable types
-- Also we may want to add a table to map index to variables and variables to index
newBddMgrFull :: Bool -> Int -> Int -> Int -> Int -> Int -> IO BddMgr
newBddMgrFull reorder numVars numZVars numSlots cacheSize maxMemory =
    do
    mgr <- hcuddInit (fromBool reorder) (castI numVars) (castI numZVars) (castI numSlots) (castI cacheSize) (castI maxMemory)
    newForeignPtr hcuddManagerDestructor mgr

newBddMgr :: IO BddMgr
newBddMgr =  newBddMgrFull True 0 0 256 262144 0


nullBddMgr :: IO BddMgr
nullBddMgr = do
             mgr <- hcuddNull
             newForeignPtr hcuddNoOpDestructor mgr


bddVarCount :: BddMgr -> Int
bddVarCount = castI . hcuddVarCount . xBddMgr


-- internal functions to grab the real ptr from the foreign pointer.
xBddMgr :: BddMgr -> XBddMgr
xBddMgr mgr = unsafeForeignPtrToPtr mgr

toBddPtr :: Bdd -> XBddPtr
toBddPtr = unsafeForeignPtrToPtr


wrapBddVar :: XBddPtr -> IO Bdd
wrapBddVar xp = newForeignPtr hcuddBddDestructor xp


bddNewVar :: BddMgr -> IO Bdd
bddNewVar mgr = let pmgr = xBddMgr mgr
                in do let gf = hcuddBddNewVar pmgr
                      r <- throwIfNull "Unable to create BDD variable\n"  gf >>=  wrapBddVar
                      touchForeignPtr mgr
                      return r

bddNewVarAtLevel :: BddMgr -> Int -> IO Bdd
bddNewVarAtLevel mgr level = let pmgr = xBddMgr mgr
                             in do
                                let gf = hcuddBddNewVarAtLevel pmgr (castI level)
                                r <- throwIfNull "Unable to create BDD variable\n" gf >>= wrapBddVar
                                touchForeignPtr mgr
                                return r

bddGetVar :: BddMgr -> Int -> IO Bdd
bddGetVar mgr index = do
                      r <- hcuddBddIthVar (xBddMgr mgr) (castI index) >>= wrapBddVar
                      touchForeignPtr mgr
                      return r

bddGetLevel :: BddMgr -> Int -> IO Int
bddGetLevel mgr index = do
                        r <- hcuddGetLevel (xBddMgr mgr) (castI index) >>= return . castI
                        touchForeignPtr mgr
                        return r

bddGetIndex :: Bdd -> IO Int
bddGetIndex bdd = withForeignPtr bdd hcuddNodeReadIndex >>= return . castI


bddSupportSize :: Bdd -> IO Int
bddSupportSize bdd = do
               withForeignPtr bdd hcuddSupportSize  >>= return . castI


bddDagSize :: Bdd -> IO Int
bddDagSize bdd = do
               withForeignPtr bdd hcuddDagSize  >>= return . castI

bddDagRatio :: Bdd -> IO Double
bddDagRatio bdd = do
               withForeignPtr bdd hcuddDagRatio >>= return . castD

bddStats :: Bdd -> IO BddStat
bddStats bdd = do
         let
            pbdd = toBddPtr bdd
         ssize <- hcuddSupportSize pbdd >>= return . castI
         dsize <- hcuddDagSize pbdd >>= return . castI
         dr    <- hcuddDagRatio pbdd >>= return . castD
         touchForeignPtr bdd
         return BddStat { support=ssize, dagsize=dsize, ratio=dr }

-- Boolean Operations
bddIte ::  Bdd -> Bdd -> Bdd -> IO Bdd
bddIte i t e = do
                 r <- hcuddBddIte (toBddPtr i) (toBddPtr t) (toBddPtr e) >>= wrapBddVar
                 touchForeignPtr i ; touchForeignPtr t ; touchForeignPtr e
                 return r

-- Internal function which to wrap all simple 2-operand operations
bddBinaryOp ::( XBddPtr -> XBddPtr -> IO XBddPtr) -> Bdd -> Bdd -> IO Bdd
bddBinaryOp func a b = do
                    r <- func (toBddPtr a) (toBddPtr b) >>= wrapBddVar
                    touchForeignPtr a ; touchForeignPtr b
                    return r

bddNor ::  Bdd -> Bdd -> IO Bdd
bddNor = bddBinaryOp hcuddBddNor

bddAnd :: Bdd -> Bdd -> IO Bdd
bddAnd = bddBinaryOp  hcuddBddAnd

bddOr :: Bdd -> Bdd -> IO Bdd
bddOr = bddBinaryOp  hcuddBddOr

bddXor :: Bdd -> Bdd -> IO Bdd
bddXor = bddBinaryOp  hcuddBddXor

bddXnor :: Bdd -> Bdd -> IO Bdd
bddXnor = bddBinaryOp  hcuddBddXNor

bddNand :: Bdd -> Bdd -> IO Bdd
bddNand = bddBinaryOp  hcuddBddNand

bddIntersect :: Bdd -> Bdd -> IO Bdd
bddIntersect = bddBinaryOp  hcuddBddIntersect

bddNot :: Bdd -> IO Bdd
bddNot a = withForeignPtr a hcuddBddNot >>= wrapBddVar

bddImplies :: Bdd -> Bdd -> IO Bdd
bddImplies a c =  do
                   r <- hcuddBddNot (toBddPtr a) >>= (hcuddBddOr (toBddPtr c)) >>= wrapBddVar
                   touchForeignPtr a ; touchForeignPtr c
                   return r

bddBiImplication :: Bdd -> Bdd -> IO (Bool, Bool)
bddBiImplication  a b = do
  aimpB <- hcuddLeq (toBddPtr a) (toBddPtr b)
  bimpA <- hcuddLeq (toBddPtr b) (toBddPtr a)
  touchForeignPtr a ; touchForeignPtr b
  return (aimpB, bimpA)

bddTrue :: BddMgr -> IO Bdd
bddTrue mgr = let pmgr = xBddMgr mgr
              in do
                 r <- hcuddReadOne pmgr >>= wrapBddVar
                 touchForeignPtr mgr
                 return r

bddFalse :: BddMgr -> IO Bdd
bddFalse mgr = let
               pmgr = xBddMgr mgr
               in do
               r <- hcuddReadZero pmgr >>= wrapBddVar
               touchForeignPtr mgr
               return r

bddTrueFalse :: BddMgr -> Bool -> IO Bdd
bddTrueFalse mgr value =
                           if value then bddTrue mgr else bddFalse mgr
                           -- touch FP is done in bddTrue/bddFalse

bddPrintMinterms :: Bdd -> IO (Int)
bddPrintMinterms  b = do
                      hFlush stdout
                      r <- withForeignPtr b hcuddPrintMinterm
                      hFlush stdout
                      return (castI r)

bddCountMinterms :: Bdd -> Int -> IO Double
bddCountMinterms b numberOfTerms = do
                    r <- hcuddCountMinterm (toBddPtr b) (castI numberOfTerms)
                    touchForeignPtr b
                    return $ castD r


bddAndList :: BddMgr ->  [Bdd] -> IO Bdd
bddAndList mgr alist =
               let
                pmgr = xBddMgr mgr

               in do
                ic <- hcuddReadOneRaw pmgr
                rawPtr <- foldM hcuddRawAnd ic (map toBddPtr alist)
                r <- hcuddToXBddPtr pmgr rawPtr >>= wrapBddVar
                mapM_ touchForeignPtr alist
                touchForeignPtr mgr
                return r

bddOrList :: BddMgr -> [Bdd] -> IO Bdd
bddOrList mgr alist =
               let
                pmgr = xBddMgr  mgr
               in do
                ic <- hcuddReadZeroRaw pmgr
                rawPtr <- foldM hcuddRawOr ic (map toBddPtr alist)
                r <- hcuddToXBddPtr pmgr rawPtr >>= wrapBddVar
                mapM_ touchForeignPtr alist
                touchForeignPtr mgr
                return r

bddXorList :: BddMgr -> [Bdd] -> IO Bdd
bddXorList mgr alist =
               let
                pmgr = xBddMgr mgr
               in do
                ic <- hcuddReadZeroRaw pmgr
                rawPtr <- foldM hcuddRawXor ic (map toBddPtr alist)
                r <- hcuddToXBddPtr pmgr rawPtr >>= wrapBddVar
                mapM_ touchForeignPtr alist
                touchForeignPtr mgr
                return r


bddIsComplement ::  Bdd -> IO Bool
bddIsComplement b = withForeignPtr b hcuddIsComplement


-- This returns Nothing if the incoming bdd is null
bddIsTrue :: Bdd -> IO (Maybe Bool)
bddIsTrue bdd = do
                let pbdd = toBddPtr bdd
                res <- hcuddIsTrue pbdd
                isnull <- hcuddIsNull pbdd
                touchForeignPtr bdd
                return $ if ( isnull ) then Nothing else Just res

bddIsFalse :: Bdd -> IO (Maybe Bool)
bddIsFalse bdd = do
                let pbdd = toBddPtr bdd
                res <- hcuddIsFalse pbdd
                isnull <- hcuddIsNull pbdd
                touchForeignPtr bdd
                return $ if ( isnull ) then Nothing else Just res

-- Return Just True or Just False if the bdd is const
bddIsConst :: Bdd -> IO (Maybe Bool)
bddIsConst bdd = do
                let pbdd = toBddPtr bdd
                isConst <- hcuddIsConstant pbdd
                isCompl <- hcuddIsComplement pbdd
                isnull <- hcuddIsNull pbdd
                touchForeignPtr bdd
                return $ if ( not isnull && isConst ) then Just (not isCompl) else Nothing


-- Create a bdd vector of width with constant value c
-- the vectors is ordered with the LSB at the head of the list.
bddConstVector :: BddMgr -> Integer -> Integer -> IO [Bdd]
bddConstVector mgr width value = do
                                   let
                                     nextBit :: (Integer,Integer) -> (Integer,Integer) -> (Integer,Integer)
                                     nextBit (xvalue,_) (_,_)  = quotRem  xvalue 2

                                     slist = replicate (fromInteger width) (value,0)
                                     values =  tail $ map snd $ scanl nextBit (value,0) slist
                                     boolvalue =  map (\i -> i /= 0 ) values
                                   mapM (bddTrueFalse mgr) boolvalue
                                  -- touchForeignPtr is done in bddTrueFalse

-- Create a bdd which represent the relation alist <= blist, where alist and blist are vectors of bdds
-- with the LSB at the head of the lists.
bddULEVector :: BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddULEVector = bddULTEVector False



-- Create a bdd which represent the relation alist < blist, where alist and blist are vectors of bdds
-- with the LSB at the head of the lists.
bddULTVector :: BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddULTVector =  bddULTEVector True

-- Helper function for bddULTVector and bddULEVector -- since the code is fully common
bddULTEVector :: Bool ->  BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddULTEVector bLTLE mgr alist blist = do
                             let
                                pmgr = xBddMgr mgr

                                bddULE prev (a,b)  = hcuddRawULEBit prev a b
                                pairs = zip (map toBddPtr alist) (map toBddPtr blist)

                             ic <- if bLTLE then hcuddReadZeroRaw pmgr else  hcuddReadOneRaw pmgr
                             rawPtr <- foldM bddULE  ic pairs
                             r <- hcuddToXBddPtr pmgr rawPtr >>= wrapBddVar
                             mapM_ touchForeignPtr alist
                             mapM_ touchForeignPtr blist
                             touchForeignPtr mgr
                             return r

bddSLEVector :: BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddSLEVector = bddSLTEVector False

bddSLTVector :: BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddSLTVector = bddSLTEVector True

bddSLTEVector :: Bool -> BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddSLTEVector bLTLE mgr as bs =
    do
    let
      (amsb:ar) = reverse as
      (bmsb:br) = reverse bs
    -- build (a & ~b) || (a == b) & prev
    prev <- bddULTEVector bLTLE mgr (reverse ar) (reverse br)
    t1 <- bddNot bmsb >>= (bddAnd amsb)
    t2 <- bddXnor  amsb bmsb >>= (bddAnd prev)
    touchForeignPtr mgr
    mapM_ touchForeignPtr as
    mapM_ touchForeignPtr bs
    bddOr t1 t2


-- subtracts  blist from alist, and returns the bdd list representing the result.
bddSubVector :: BddMgr -> [Bdd] -> [Bdd] -> IO [Bdd]
bddSubVector = bddAddSubVector False

-- adds blist to alist and returns the bdd list representing the sum
bddAddVector :: BddMgr -> [Bdd] -> [Bdd] -> IO [Bdd]
bddAddVector = bddAddSubVector True

bddAddSubVector :: Bool -> BddMgr -> [Bdd] -> [Bdd] -> IO [Bdd]
bddAddSubVector bAddSub mgr alist blist = do
                       let
                            pmgr = xBddMgr mgr
                            pairs = zip (map toBddPtr alist) (map toBddPtr blist)

                       ic <- if ( bAddSub ) then hcuddReadZeroRaw pmgr else hcuddReadOneRaw pmgr
                       dummy <-  hcuddReadOne pmgr
                       rawPairs <- scanlM (bddAddCarryRaw bAddSub pmgr) (ic,dummy) pairs --[(RawBddPtr,XBddPtr)]
                       r <- mapM  wrapBddVar ( snd (unzip (tail rawPairs)) )

                       -- TODO need to deref final result ?? is this done?
                       let dangling = snd (head rawPairs )
                       hcuddDestroyBdd dangling

                       mapM_ touchForeignPtr alist
                       mapM_ touchForeignPtr blist
                       touchForeignPtr mgr

                       return r


bddIteVector :: Bdd -> [Bdd] -> [Bdd] -> IO [Bdd]
bddIteVector c thens elses =
             mapM (\(t,e) -> bddIte c t e) (zip thens elses)
             -- foreign ptr are touched in bddIte

-- Monadic scanl function -- this should probably go into Utils
scanlM :: (a -> b -> IO a) -> a -> [b] -> IO [a]
scanlM op ic xlist = case xlist of
                   []     -> return [ic]
                   x:xs   -> do
                                rv <- op ic x >>= (\nv -> scanlM op nv xs)
                                return ( ic : rv )


bddAddCarryRaw :: Bool -> XBddMgr -> (RawBddPtr, XBddPtr) -> (XBddPtr,XBddPtr) -> IO (RawBddPtr, XBddPtr )
bddAddCarryRaw bAddSub pmgr (cin,_) (a, b) = do
                    hcuddRef cin        -- need to update reference count since this
                                        -- is decremented in each of the next 2 calls
                    ssum  <- hcuddRawAddBit (fromBool bAddSub) cin a b >>= hcuddToXBddPtr pmgr
                    cout <- hcuddRawCoutBit (fromBool bAddSub) cin a b
                    return (cout, ssum)


-- creates a bdd which is the logical equal of the 2 vectors.
bddEQVector :: BddMgr -> [Bdd] -> [Bdd] -> IO Bdd
bddEQVector mgr alist blist = do
                     bitWise <- zipWithM bddXnor alist blist
                     r <- bddAndList mgr bitWise
                     mapM_ touchForeignPtr alist
                     mapM_ touchForeignPtr blist
                     touchForeignPtr mgr
                     return r


-- Not a safe public interface since this can throw an error use bddGetModel
-- Use bddGetModel
bddGetThen ::  Bdd -> IO (Bdd)
bddGetThen b =
           let
               pbdd = toBddPtr b
           in do
              constNode <- hcuddIsConstant pbdd
              r <- if constNode then (error "Cannot get then part of a constant bddGetThen")
                           else hcuddBddThen pbdd >>= wrapBddVar
              touchForeignPtr b
              return r

-- Not a safe public interface
bddGetElse :: Bdd -> IO (Bdd)
bddGetElse b =
           let
               pbdd = toBddPtr b
            in do
              constNode <- hcuddIsConstant pbdd
              r <- if ( constNode ) then ( error "Cannot get else part of a constant bddGetElse")
                               else hcuddBddElse pbdd >>= wrapBddVar
              touchForeignPtr b
              return r

bddGetModel ::  Bdd -> IO BddModel
bddGetModel b =
            let
                pbdd = toBddPtr b
            in do
                bid <- hcuddNodeReadIndex pbdd
                constNode <- hcuddIsConstant pbdd
                complementNode <- hcuddIsComplement pbdd
                r <- if constNode then (return (BddLeaf $ not complementNode ))
                             else do
                                t <- bddGetThen b
                                e <- bddGetElse b
                                return (BddNode bid complementNode t e)
                touchForeignPtr b
                return r


bddGetModelUnsafe :: RawBddPtr -> BddModelInternal
bddGetModelUnsafe pbdd =
                  let
                    constNode = hcuddIsConstantRaw pbdd
                    complementNode = hcuddIsComplementRaw pbdd
                    bid = hcuddNodeReadIndexRawUnsafe pbdd
                  in
                    if constNode then (IBddLeaf $ not complementNode )
                             else IBddNode bid complementNode t e
                                    where
                                    t = hcuddBddThenRawUnsafe pbdd
                                    e = hcuddBddElseRawUnsafe pbdd


-- Note that a linear sized bdd, can produce an exponential sized string!
showBdd :: ( Int -> String ) -> Bdd -> IO String
showBdd f b = let
                bddModel = bddGetModelUnsafe (hcuddGetRawUnsafe (toBddPtr b ) )
                printExpr = bddPrinterR f bddModel
                r = show printExpr
              in do
                touchForeignPtr b
                return r


-- Note that a linear sized bdd, can produce an exponential sized string!
showBddList :: (Int -> String ) -> [Bdd] -> IO String
showBddList f bs = do
            strs <- mapM (showBdd f) bs
            return $ "[" ++ (concatMap (++ ",") strs) ++ "]"


printExprInv :: Bool -> PrintExpr -> PrintExpr
printExprInv True  (Prod str) = Prod (negateP str)
printExprInv True  (Sum  str) = Prod (negateP str)
printExprInv True  (Term str) = Prod (negateStr str)
printExprInv False  e = e
printExprInv True _ = error ("printExprInv: unexpected pattern" )

bddPrinterR :: (Int -> String) -> BddModelInternal -> PrintExpr
bddPrinterR _ (IBddLeaf n) =  if n then Const1 else Const0
bddPrinterR f (IBddNode bid c t e) =
               let
                  varName = f (castI bid)
                  tm = bddGetModelUnsafe t
                  ts = bddPrinterR f tm
                  em = bddGetModelUnsafe e -- BddModel
                  es = bddPrinterR f em -- PrintExpr
               in
                  printExprInv c (joinPrintExpr varName ts es)


paren :: String -> String
paren s = "(" ++ s ++ ")"
negateStr :: String -> String
negateStr s = "~" ++ s
negateP :: String -> String
negateP s = "~(" ++ s ++ ")"
andStr :: String -> String -> String
andStr a b = a ++ "&" ++ b
andStrP :: String -> String -> String
andStrP a b = "(" ++ (andStr a b) ++ ")"
orStr :: String -> String -> String
orStr a b = a ++ "|" ++ b

joinPrintExpr :: String -> PrintExpr -> PrintExpr -> PrintExpr

joinPrintExpr v Const0  Const0   = error "C0 C0 not expected in joinPrintExpr"
joinPrintExpr v Const0  Const1   = Term (negateStr v)
joinPrintExpr v Const0  (Prod e) = Prod (andStr (negateStr v) e)
joinPrintExpr v Const0  (Sum e)  = Prod (andStr (negateStr v) (paren e))
joinPrintExpr v Const0  (Term e) = Prod (andStr (negateStr v) e)

joinPrintExpr v Const1  Const0   = Term  v
joinPrintExpr v Const1  Const1   = error "C1 C1 not expected in joinPrintExpr"
joinPrintExpr v Const1  (Prod e) = Sum  (orStr  v (paren e))
joinPrintExpr v Const1  (Sum e)  = Sum  (orStr  v e)
joinPrintExpr v Const1  (Term e) = Sum  (orStr  v e)

joinPrintExpr v (Prod t)  Const0   = Prod (andStr v t)
joinPrintExpr v (Prod t)  Const1   = Sum  (orStr (negateStr v) t)
joinPrintExpr v (Prod t)  (Prod e) = Sum  (orStr (andStrP v t) (andStrP (negateStr v) e))
joinPrintExpr v (Prod t)  (Sum e)  = Sum  (orStr (andStrP v t) (andStrP (negateStr v) (paren e)))
joinPrintExpr v (Prod t)  (Term e) = Sum  (orStr (andStrP v t) (andStrP (negateStr v) e))

joinPrintExpr v (Sum  t)  Const0   = Prod (andStr v (paren t))
joinPrintExpr v (Sum  t)  Const1   = Sum  (orStr (negateStr v) t)
joinPrintExpr v (Sum  t)  (Prod e) = Sum  (orStr (andStrP v t) (andStrP (negateStr v) e))
joinPrintExpr v (Sum  t)  (Sum e)  = Sum  (orStr (andStrP v t) (andStrP (negateStr v) (paren e)))
joinPrintExpr v (Sum  t)  (Term e) = Sum  (orStr (andStrP v t) (andStrP (negateStr v) e))

joinPrintExpr v (Term t)  Const0   = Prod (andStr v t)
joinPrintExpr v (Term t)  Const1   = Sum  (orStr (negateStr v) t)
joinPrintExpr v (Term t)  (Prod e) = Sum  (orStr (andStrP v t) (andStrP (negateStr v) e))
joinPrintExpr v (Term t)  (Sum e)  = Sum  (orStr (andStrP v t) (andStrP (negateStr v) (paren e)))
joinPrintExpr v (Term t)  (Term e) = Sum  (orStr (andStrP v t) (andStrP (negateStr v) e))


dotDump :: Bdd -> IO ()
dotDump b = withForeignPtr b hcuddDotDump

dummyP :: Int -> String
dummyP vid = "b" ++ show (vid +1)

tester :: IO ()
tester =
       let
         pbdd :: String -> Bdd -> IO ()
         pbdd s b= do putStr $ s ++ " "
                      showBdd dummyP b >>= putStrLn

         pbddL :: String -> [Bdd] -> IO ()
         pbddL s bs = let

                      in do
                        putStrLn s
                        mapM_ (\ b -> do showBdd dummyP b >>= putStrLn ; bddPrintMinterms b) bs
                        putStrLn $ "End " ++ s

       in do
        mgr <- newBddMgr
        b1 <-  bddNewVar mgr
        b2 <-  bddNewVar mgr
        b3 <-  bddNewVar mgr
        b4 <-  bddNewVar mgr
        b5 <-  bddNewVar mgr
        b6 <-  bddNewVar mgr
        b7 <-  bddNewVar mgr
        b8 <-  bddNewVar mgr
        b9 <-  bddNewVar mgr
        bd <-  bddIte b2 b3 b4
--        be <- bddAnd (bddOr b1 b2) (bddOr (bddNot b3) b4)
        be <- bddImplies b1 b2
        pbdd " be is :" be
        putStr "bd = Ite b2 b3 b4\n"
        pbdd "bd " bd

        bdN <- bddNot bd
        pbdd "bdN is:" bdN
        dotDump bdN

--        bddPrintMinterms bd

        t <- bddTrue mgr
        f <- bddFalse mgr

        pbdd "Bdd true prints as:" t
        pbdd "Bdd false prints as:" f

        t1 <- bddIsTrue t
        t2 <- bddIsFalse t
        t3 <- bddIsTrue f
        t4 <- bddIsFalse f
        t5 <- bddIsTrue bd
        t6 <- bddIsFalse b1
        putStrLn "t is bddTrue "
        putStrLn $ foldr (++) " " (intersperse " " (map show  [t1,t2,t3,t4,t5,t6]) )
        --
        let tbs = [t, f, bd, b1]
        tx <- mapM bddIsConst tbs
        putStrLn "test bddIsConst "
        putStrLn $ foldr (++) " " (intersperse " " (map show tx) )

        bB <- bddAndList mgr [b1, b2, b5]
        pbdd "Truth table for bddAndList b1 b2 b5" bB
        _ <- bddPrintMinterms bB
        putStr "\n"

        bC <- bddOrList mgr [b1, b2, b5]
        pbdd "bC is: " bC


        bD <- bddAnd bdN b1
        pbdd "bD is: " bD

        c13 <- bddConstVector mgr 8 13
        mapM_ (pbdd  "c13: ") c13


        c4 <- bddConstVector mgr 4 13
        mapM_ (pbdd  "c4: ") c4
        let v1 = reverse [b1,b2,b3,b4]
        let v2 = reverse [b5,b6,b7,b8]

        ule <- bddULEVector mgr v1 c4
        pbdd "ule " ule
        _ <- bddPrintMinterms ule

        ult <- bddULTVector mgr v1 c4
        pbdd "ult " ult
        _ <- bddPrintMinterms ult


        slt <- bddSLTVector mgr v1 v2
        pbdd "slt " slt
        _ <- bddPrintMinterms slt


        sle <- bddSLEVector mgr v1 v2
        pbdd "sle " sle
        _ <- bddPrintMinterms sle

        v1mv2 <- bddSubVector mgr v1 v2
        c0 <- bddConstVector mgr 4 0
        cmp1 <- bddULTVector mgr v1mv2 c0

        putStrLn $ "v1 - v2  is:"
        mapM_ bddPrintMinterms  v1mv2


        putStrLn $ "v1 - v2 > 0 is:"
        _ <- bddPrintMinterms cmp1

        testout <- scanlM testScanM "Start" ['a','b','c','d','e']
        putStrLn $ "testout is" ++ (unlines testout )


        let foo2 = scanl testScan "Start" ['a','b','c','d','e']
        putStrLn $ "foo2 is" ++ (unlines foo2 )

        addv1c4 <- bddAddVector mgr v1 c4
        pbddL "addv1C4 "  addv1c4


        subv1c4 <- bddSubVector mgr v1 c4
        pbddL "subv1C4 "  subv1c4
        --
        -- Test Bi implication
        bimp0 <- bddBiImplication be bd
        putStrLn $ "biIMplication be bd is " ++ show bimp0

        bimp1 <- bddBiImplication bd be
        putStrLn $ "biIMplication bd be is " ++ show bimp1

        bimp2 <- bddBiImplication bd bd
        putStrLn $ "biIMplication bd bd is " ++ show bimp2

        bimp3 <- bddBiImplication b1 b2
        putStrLn $ "biIMplication b1 b2 is " ++ show bimp3

        bimp4 <- bddBiImplication bB bC
        putStrLn $ "biIMplication bB bC is " ++ show bimp4

        bimp5 <- bddBiImplication bC bB
        putStrLn $ "biIMplication bC bB is " ++ show bimp5

        bimp6 <- bddBiImplication b1 be
        putStrLn $ "biIMplication b1 be is " ++ show bimp6
        bimp7 <- bddBiImplication b2 be
        putStrLn $ "biIMplication b2 be is " ++ show bimp7


        let xx1 = RawBdd
            yy1 = XBddM
            zz1 = XBddP
        sinkvar xx1 yy1 zz1
        putStr "End of Bdd op\n\n\n"

-- silence the compiler.
sinkvar :: RawBdd -> XBddM -> XBddP -> IO()
sinkvar x y z = return ()

testScanM :: String -> Char -> IO String
testScanM  s c = do
                                putStr $ "c is " ++ [c]
                                return (s ++ [' ',c])


testScan :: String -> Char -> String
testScan  s c =  (s ++ [' ',c])
