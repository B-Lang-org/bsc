module Synthesize(aSynthesize) where

import Data.List(transpose, sort, genericLength, nub)
import Control.Monad(when, zipWithM, zipWithM_)
import Control.Monad.State(State, runState, gets, get, put)
import Debug.Trace
import qualified Data.Map as M

import Util(integerToBits, makePairs, log2, itos)
import PPrint
import IntLit
import ErrorUtil
import Flags(Flags, synthesize)
import Position(noPosition)
import FStringCompat(mkFString)
import Id
import Prim
import Pragma(DefProp, defPropsHasNoCSE)
import ASyntax
import ASyntaxUtil(tsortADefs, aType, isConst, aSize, )
import AExpand(aSRemoveUnused)
import AOpt(aOptBoolExpr)
import IOUtil(progArgs)

doTrace :: Bool
doTrace = elem "-trace-syn" progArgs

-- ---------------
-- Naming conventions

synthPref :: String
synthPref = "_dw"

-- ---------------

aSynthesize :: Flags -> ASPackage -> ASPackage
aSynthesize flags p@(ASPackage { aspkg_values = ds }) =
    if not (synthesize flags) then
        p
    else
        -- XXX use some fast removal of unused defs & renamings.
        aImprove (p { aspkg_values = synDefs ds })

-- ---------------

-- Improve by iterating the following steps:
--   remove unused definitions
--   inline variables and constants
--   propagate constants
-- XXX - assuming foreign function calls need not be touched because state variable instantiations are not touched
aImprove :: ASPackage -> ASPackage
aImprove p@(ASPackage { aspkg_values = ds }) =
    let inline :: M.Map AId AExpr
        inline = M.fromList [ (i, e) | ADef i _ e _ <- ds, isSimple e ]
        repl :: AExpr -> AExpr
        repl e@(ASDef _ i) =
                case M.lookup i inline of
                Just e' -> e'
                Nothing -> e
        repl (APrim aid t p es) = APrim aid t p (map repl es)
        repl (ANoInlineFunCall t i f es) = ANoInlineFunCall t i f (map repl es)
        repl (AFunCall t i f isC es) = AFunCall t i f isC (map repl es)
--        repl e = internalError ("aImprove.replE " ++ ppReadable e)
        repl e = e
        -- aOptBoolExpr is overkill...
        ds' = [ ADef i t (aOptBoolExpr (repl e)) p | ADef i t e p <- ds ]
        p'' = aSRemoveUnused False (p { aspkg_values = ds' })
        ds'' = aspkg_values p''
    in  if length ds == length ds'' && ds == ds'' then        -- length check is a fast check for inequality
            (if doTrace then trace "aImprove done" else id)
            p
        else
            (if doTrace then trace ("aImprove iterates, " ++ show (length ds, length ds'')) else id) $
--          trace (ppReadable p'') $
            aImprove p''

--------

data SState = SState {
                -- unique name generator
                uniqueId :: Integer,
                -- definitions processed so far
                -- at the end, these become the defs of the resulting module
                defs :: [(AId, AExpr, [DefProp])],
                -- reverse lookup of defs processed or added so far,
                -- to avoid creating new Ids for exprs which already had Ids
                -- (defs marked NoCSE are not added to this map)
                cse_map :: (M.Map AExpr AId),
                -- map of defs which have been deemed "simple"
                -- (references to these can be inlined with the expression)
                simple_map :: (M.Map AId AExpr)
              }

type S a = State SState a

addDef :: AId -> AExpr -> [DefProp] -> S ()
addDef v e props = do
  state <- get
  ds <- gets defs
  cmap <- gets cse_map
  smap <- gets simple_map
  let ds' = ((v,e,props):ds)
      cmap' = if (defPropsHasNoCSE props)
              then cmap
              else M.insert e v cmap
      smap' = case isSimple e of
                True -> M.insert v e smap
                _ -> smap
  put $ state { defs = ds', cse_map = cmap', simple_map = smap' }

getSimple :: AId -> AExpr -> S AExpr
getSimple v e = do
  smap <- gets simple_map
  return $ M.findWithDefault e v smap

findExpr :: AExpr -> S (Maybe AId)
findExpr e = do
  cmap <- gets cse_map
  return $ M.lookup e cmap

getDefs :: S [(AId, AExpr, [DefProp])]
getDefs = do
  state <- get
  ds <- gets defs
  put $ state { defs = [], cse_map = M.empty }
  return $ reverse ds

newName :: S AId
newName = do
  state <- get
  i <- gets uniqueId
  put $ state { uniqueId = (i+1) }
  return $ mkId noPosition (mkFString ("_ds" ++ itos i))

--------

synDefs :: [ADef] -> [ADef]
synDefs ds =
    let initState = SState { uniqueId = 1,
                             defs = [],
                             cse_map = M.empty,
                             simple_map = M.empty
                           }
    in  fst $ runState (synDefsS (tsortADefs ds)) initState

synDefsS :: [ADef] -> S [ADef]
synDefsS ds = do
    mapM_ toED ds
    ies <- getDefs
    mapM_ synDef ies
    ies' <- getDefs
    when doTrace $ trace ("synDefsS done") $ return ()
    return [ ADef i (aType e) (e) p | (i, e, p) <- ies' ]

toED :: ADef -> S ()
toED (ADef i t e props) = do
    e' <- toE e
    addDefU i e' props

toE :: AExpr -> S AExpr
-- XXX bad code
toE (APrim aid t p [x,y]) | p == PrimSLE || p == PrimSLT =
        let ty = aType x
            n = case ty of
                  (ATBit sz) -> sz
                  _ -> internalError "Synthesize.toE PrimSLx: n"
            c = ASInt defaultAId ty (ilHex (2^(n-1)))
            x' = APrim aid ty PrimXor [x, c]
            y' = APrim aid ty PrimXor [y, c]
        in  toE (APrim aid t (if p == PrimSLE then PrimULE else PrimULT) [x',y'])
-- XXX bad code
toE (APrim aid t@(ATBit n) PrimExtract [e, h, l]) | h /= l && not (isConst h && isConst l) =
        let te = aType e
            m = case te of
                  (ATBit sz) -> sz
                  _ -> internalError "Synthesize.toE PrimExtract: m"
            e1 | m > n     = APrim aid t PrimExtract
                                [e1f,
                                 ASInt defaultAId aTNat (ilDec (n-1)),
                                 ASInt defaultAId (aType h) (ilDec 0)]
               | n < m     = APrim aid t PrimZeroExt [e1f]
               | otherwise = e1f
            e1f = APrim aid te PrimSRL [e, l]
            e2 = APrim aid t PrimSub
                        [onesh,
                        ASInt defaultAId t (ilDec 1)]
            onesh = APrim aid t PrimSL
                        [ASInt defaultAId t (ilDec 1),
                         shft]
            shft = APrim aid (aType h) PrimAdd
                        [hml,
                         ASInt defaultAId (aType h) (ilDec 1)]
            hml = APrim aid (aType h) PrimSub [h, l]
            e' = aOptBoolExpr (APrim aid t PrimAnd [e1, e2])
        in  toE e'
toE (APrim aid t p es) = mapM toSE es >>= return . APrim aid t p
toE (ANoInlineFunCall t i f es) = mapM toSE es >>= return . ANoInlineFunCall t i f
toE (AFunCall t i f isC es) = mapM toSE es >>= return . AFunCall t i f isC
toE e = return e

toSE :: AExpr -> S AExpr
toSE (ASAny t _) = return (ASInt defaultAId t (ilDec 0))
toSE e@(ASInt {}) = return e
toSE e@(ASStr {}) = return e
toSE e@(ASDef {}) = return e
toSE e@(ASPort {}) = return e
toSE e@(ASParam {}) = return e
toSE e = do
    e' <- toE e
    i <- addExpr e'
    return (ASDef (aType e') i)

addExpr :: AExpr -> S AId
addExpr e = do
    e' <- normExpr e
    mi <- findExpr e'
    case mi of
     Just i -> return i
     Nothing -> do
        i <- newName
        addDef i e' []
        return i

addDefU :: AId -> AExpr -> [DefProp] -> S ()
addDefU i e p = do
    e' <- normExpr e
    mi <- findExpr e'
    case mi of
     Just oi -> addDef i (ASDef (aType e') oi) p
     Nothing -> addDef i e' p

-- put primops on "normal form", i.e., with sorted operands and simple id inlined
normExpr :: AExpr -> S AExpr
normExpr (APrim aid t op es) = do
    let getSimpleS e@(ASDef _ i) = getSimple i e
        getSimpleS e = return e
    es' <- mapM getSimpleS es
    return (sortExpr (aOptPrim aid t op es'))
normExpr e@(ASDef _ i) = getSimple i e
normExpr e = return e

aOptPrim :: AId -> AType -> PrimOp -> [AExpr] -> AExpr
aOptPrim aid t PrimBAnd es  = aAnds aid es
aOptPrim aid t PrimBOr  es  = aOrs  aid es
aOptPrim aid t PrimXor  es  = aXors aid es
aOptPrim aid t PrimBNot [e] = aNot aid e
aOptPrim aid t p es = APrim aid t p es

sortExpr :: AExpr -> AExpr
sortExpr (APrim aid t op es) | isGate op = APrim aid t op (sort es)
  where isGate op = op `elem` [PrimBAnd, PrimBOr, PrimXor]
sortExpr e = e

wireId :: Id -> Int -> Id
wireId i n = mkIdPre (mkFString (synthPref ++ itos n ++ "_")) i

synDef :: (AId, AExpr, [DefProp]) -> S ()
synDef (i, e, props) = do
    when doTrace $ trace ("synDef " ++ ppReadable (i, e)) $ return ()
    es <- synExp e
    case es of
     [e'] -> addDefU i e' props
     es -> do
        let is = map (wireId i) [0..length es-1]
        zipWithM_ (\i e -> addDefU i e props ) is es
--        trace (ppReadable (is, es)) $ return ()
        addDefU i (APrim i (aType e) PrimConcat (map (ASDef aTBool) (reverse is))) props

synExp :: AExpr -> S [AExpr]
synExp (APrim aid t p es) = synPrim aid t p es
synExp e@(ANoInlineFunCall t _ _ _) = do
        i <- newName
        addDef i e []
        --trace ("synExp: ANoInlineFunCall " ++ ppReadable (i, e)) $ return ()
        return (splitASDef t i)
synExp e@(AFunCall t _ _ _ _) = do
        i <- newName
        addDef i e []
        --trace ("synExp: AFunCall " ++ ppReadable (i, e)) $ return ()
        return (splitASDef t i)

-- task calls and task values do not simplify
synExp e@(ATaskValue { }) = return [ e ]
synExp v@(ASPort (ATBit 1) i) = return [ v ]
synExp (ASPort t i) = return (splitASPort t i)
-- XXX parameters don't need simplifying?
-- XXX if we didn't know "t", we wouldn't be able to split
-- synExp (ASParam t i) = return (splitASParam t i)
synExp v@(ASParam t i) = return [ v ]
--synExp (ASDef t i) = return (splitASDef t i)
synExp v@(ASDef (ATBit 1) i) = return [ v ]
synExp (ASDef (ATBit n) i) = return [ ASDef aTBool (wireId i k) | k <- [0..fromInteger n-1] ]
synExp (ASInt aid (ATBit n) (IntLit _ _ i)) = return [ ASInt aid aTBool (ilSizedBin 1 b) | b <- reverse (integerToBits n i) ]
synExp (ASStr _ _ _) = internalError "Synthesize.synExp: ASStr"
synExp (ASAny t _) = internalError "Synthesize.synExp: ASAny"
synExp _ = internalError( "Synthesize::synExp" )

synExpS :: AExpr -> S [AExpr]
synExpS e = synExp e >>= toSs

-- ---------------

splitASDef :: AType -> AId -> [AExpr]
splitASDef t i = splitVar t i (ASDef t i)

splitASPort :: AType -> AId -> [AExpr]
splitASPort t i = splitVar t i (ASPort t i)

-- Create a list of expressions returning the bits of a variable "v"
-- (the "v" can be either ASDef or ASPort, with name "i")
splitVar :: AType -> AId -> AExpr -> [AExpr]
splitVar t@(ATBit 1) i v = [v]
splitVar t@(ATBit n) i v =
    [ APrim i aTBool PrimExtract [v, aj, aj] | j <- [0..n-1], let aj = aNat j ]
splitVar _ _ _ = internalError( "Synthesize::splitVar" )

-- ---------------

isSimple :: AExpr -> Bool
isSimple (ASInt {}) = True
isSimple (ASStr {}) = True
isSimple (ASPort {}) = True
isSimple (ASParam {}) = True
isSimple (ASDef {}) = True
isSimple (ASAny {}) = True
isSimple _ = False

toS :: AExpr -> S AExpr
toS e | isSimple e = return e
        | True = do
    i <- addExpr e
    return (ASDef (aType e) i)

toS2 :: (AExpr, AExpr) -> S (AExpr, AExpr)
toS2 (x, y) = do
    x' <- toS x
    y' <- toS y
    return (x', y')

toSs :: [AExpr] -> S [AExpr]
toSs = mapM toS

isBoolOp :: PrimOp -> Bool
isBoolOp PrimBAnd = True
isBoolOp PrimBOr = True
isBoolOp PrimBNot = True
isBoolOp _ = False

isBoolVecOp :: PrimOp -> Bool
isBoolVecOp PrimAnd = True
isBoolVecOp PrimOr = True
isBoolVecOp PrimInv = True
isBoolVecOp PrimXor = True
isBoolVecOp _ = False

primToFun :: PrimOp -> AId -> [AExpr] -> AExpr
primToFun PrimAnd = aAnds
primToFun PrimOr = aOrs
primToFun PrimInv = aNots
primToFun PrimXor = aXors
primToFun p =  internalError( "Synthesize::primToFun: " ++ (show p))


shiftOf :: PrimOp -> ShiftFun
shiftOf PrimSL = permSL
shiftOf PrimSRL = permSRL
shiftOf PrimSRA = permSRA
shiftOf p =  internalError( "Synthesize::shiftOf: " ++ (show p))

synPrim :: AId -> AType -> PrimOp -> [AExpr] -> S [AExpr]
synPrim aid t p es | isBoolOp p = return [APrim aid t p es]
synPrim aid _ p es | isBoolVecOp p = do
        ess <- mapM synExpS es
        return (map ((primToFun p) aid) (transpose ess))
--        return (map (APrim _ aTBool (vecToBool p)) (transpose ess))
synPrim aid _ PrimEQ [x, y] = do
        xs <- synExpS x
        ys <- synExpS y
        rs <- toSs (zipWith (aXor aid) xs ys)
        ne <- toS (aOrs aid rs)
        return [aNot aid ne]
synPrim aid ty PrimIf [c, t, e] = do
        notc <- toS (aNot aid c)
        synPrim aid ty PrimMux [c, t, notc, e]
synPrim aid _ PrimMux pes = synMux aid (unzip (makePairs pes))
synPrim aid _ PrimPriMux pes = do
        let (ps, es) = unzip (makePairs pes)
        ps' <- synPriEnc aid [] ps >>= toSs
        synMux aid (ps', es)
synPrim aid _ PrimExtract [e, ASInt _ _ (IntLit _ _ h), ASInt _ _ (IntLit _ _ l)] = do
        es <- synExp e
        return (take (fromInteger (h-l+1)) (drop (fromInteger l) es))
synPrim aid _ PrimExtract [e, x, x'] | x==x' = do
        es <- synExpS e
        xs <- synExpS x
        let n = log2 (length es)
        cs <- synDecode aid (take n xs) >>= toSs
        as <- toSs (zipWith (aAnd aid) cs es)
        return [aOrs aid as]
synPrim aid _ PrimConcat es = do
        ess <- mapM synExp es
        return (concat (reverse ess))
synPrim aid _ PrimRange [_,_,e] = synExp e
synPrim aid (ATBit n) PrimZeroExt [e] = do
        let k = aSize e
        es <- synExp e
        return (es ++ replicate (fromInteger (n-k)) aFalse)
synPrim aid (ATBit n) PrimSignExt [e] = do
        let k = aSize e
        es <- synExp e
        let sign = last es
        return (es ++ replicate (fromInteger (n-k)) sign)
synPrim aid _ PrimCase (c:d:ces) = do
        let n = aSize c
            pown = 2^n
            arms = [ (i,e) | (ASInt _ _ (IntLit _ _ i), e) <- makePairs ces ]
            len = genericLength arms
            missing = pown - len
            ies = if missing * n < len then fill arms [0..pown-1] else arms
            fill []             []              = []
            fill ((i, e) : ces) (k:ks) | i == k = (i, e) : fill ces ks
            fill ces            (k:ks)          = (k, d) : fill ces ks
            fill _              _               = internalError( "Synthesize::synPrim::fill" )

        cs <- synExpS c
        ncs <- mapM (toS . (aNot aid)) cs
        let mkArm bs = toS (aAnds aid (zipWith3 dec1 bs ncs cs))
            dec1 0 n _ = n
            dec1 1 _ c = c
            dec1 _ _ _ = internalError "synthesize.dec1"

        ps <- mapM mkArm (map (reverse . integerToBits n . fst) ies)
        (defp, defe) <-
                if genericLength ies == pown then
                    return ([], [])
                else do
                   o <- toS (aOrs aid ps)
                   a <- toS (aNot aid o)
                   return ([a], [d])
        synMux aid (defp ++ ps, defe ++ map snd ies)
synPrim aid _ PrimAdd [x, y] = do
        xs <- synExpS x
        ys <- synExpS y
        (_, ss) <- synXAdd aid xs ys aFalse
        return ss
synPrim aid _ PrimSub [x, y] = do
        xs <- synExpS x
        ys <- synExpS y
        (_, ss) <- synXSub aid xs ys aTrue
        return ss
synPrim aid (ATBit n) PrimNeg [y] = do
        let xs = replicate (fromInteger n) aFalse
        ys <- synExpS y
        (_, ss) <- synXSub aid xs ys aTrue
        return ss
synPrim aid (ATBit n) PrimMul [x, y] = do
        xs <- synExpS x
        ys <- synExpS y
        ss <- synMul aid xs ys
        return (take (fromInteger n) ss)
synPrim aid _ PrimULT [x, y] = do
        xs <- synExpS x
        ys <- synExpS y
        (le, _) <- synXSub aid ys xs aFalse
        return [le]
synPrim aid _ PrimULE [x, y] = do
        xs <- synExpS x
        ys <- synExpS y
        (le, _) <- synXSub aid ys xs aTrue
        return [le]
synPrim aid (ATBit n) p [x, y] | p == PrimSL || p == PrimSRL || p == PrimSRA = do
        xs <- synExpS x
        ys <- synExpS y
        synShifter aid (shiftOf p) (take (log2 (length xs)) ys) xs
-- scheduler
synPrim aid t@(ATBit n) p es =
        trace ("synPrim: unimplemented " ++ ppReadable (p,t,es)) $
        return (map (const unknown) [1..n])
  where -- XXX using a fake port reference to create a reference to 'z' value
        unknown = ASPort aTBool (mkId noPosition (mkFString "z"))

synPrim aid t p es = internalError ("synPrim: not bit: " ++ ppReadable (p,t,es))

synMux :: AId -> ([AExpr], [AExpr]) -> S [AExpr]
synMux aid (ps, es) = do
        let mux1and :: AExpr -> [AExpr] -> S [AExpr]
            mux1and p es = toSs (map (aAnd aid p) es)
        ess <- mapM synExpS es
        ess' <- zipWithM mux1and ps ess
        return (map (aOrs aid) (transpose ess'))

synPriEnc :: AId -> [AExpr] -> [AExpr] -> S [AExpr]
synPriEnc aid ns [] = return []
synPriEnc aid ns (p:ps) = do
        n <- toS (aNot aid p)
        es <- synPriEnc aid (n:ns) ps
        return (aAnds aid (p:ns) : es)

-- Make a decoder with cs input bits, returns a one-hot list.
synDecode :: AId -> [AExpr] -> S [AExpr]
synDecode aid cs = do
        ncs <- mapM (toS . (aNot aid)) cs
        let n = genericLength cs
            dec bs = (aAnds aid) (zipWith3 dec1 bs ncs cs)
            dec1 0 n _ = n
            dec1 1 _ c = c
            dec1 _ _ _ = internalError "synthesize.dec1"

        return (map (dec . reverse . integerToBits n) [0..2^n-1])

--aXors xs = foldr1 aXor xs
aXors :: AId -> [AExpr] -> AExpr
aXors aid [x, y] = aXor aid x y
aXors _ _ = internalError "Synthesize.aXors: list should be of length 2"

aXor :: AId -> AExpr -> AExpr -> AExpr
aXor aid x y | isFalse x = y
             | isTrue  x = aNot aid y
             | isFalse y = x
             | isTrue  y = aNot aid x
             | x == y    = aFalse
             | otherwise = APrim aid aTBool PrimXor [x, y]

aNots :: AId -> [AExpr] -> AExpr
aNots aid [e] = aNot aid e
aNots _ _ = internalError "Synthesize.aNots"

aNot :: AId -> AExpr -> AExpr
aNot aid e | isTrue e  = aFalse
           | isFalse e = aTrue
           | otherwise = APrim aid aTBool PrimBNot [e]

aAnds :: AId -> [AExpr] -> AExpr
aAnds aid es = if any isFalse es then aFalse else aAnds' (nub (filter (not . isTrue) es))
  where aAnds' []  = aTrue
        aAnds' [e] = e
        aAnds' es  = APrim aid aTBool PrimBAnd es

aAnd :: AId -> AExpr -> AExpr -> AExpr
aAnd aid x y = aAnds aid [x, y]

aOrs :: AId -> [AExpr] -> AExpr
aOrs aid es = if any isTrue es then aTrue else aOrs' (nub (filter (not . isFalse) es))
  where aOrs' []  = aFalse
        aOrs' [e] = e
        aOrs' es  = APrim aid aTBool PrimBOr es

aOr :: AId -> AExpr -> AExpr -> AExpr
aOr aid x y = aOrs aid [x, y]

-----

fAdd :: AId -> AExpr -> AExpr -> AExpr -> S (AExpr, AExpr)
fAdd aid a b c = do
        sab <- toS (aXor aid a b)
        ab <- toS (aAnd aid a b)
        bc <- toS (aAnd aid b c)
        ca <- toS (aAnd aid c a)
        let s = aXor aid sab c
            co = aOrs aid [ab, bc, ca]
        return (co, s)

hAdd :: AId -> AExpr -> AExpr -> S (AExpr, AExpr)
hAdd aid a b = return (aAnd aid a b, aXor aid a b)

type SynArith = AId -> [AExpr] -> [AExpr] -> AExpr -> S (AExpr, [AExpr])

-- Make a ripple carry adder
synRippleAdd :: SynArith
synRippleAdd _    []     [] ci = return (ci, [])
synRippleAdd aid (x:xs) (y:ys) ci = do
                                    (c, s) <- fAdd aid x y ci
                                    c' <- toS c
                                    (co, ss) <- synRippleAdd aid xs ys c'
                                    return (co, s:ss)
synRippleAdd _ _ _ _ = internalError "Synthesize.synRippleAdd - length xs /= length ys"

-- synRippleSub = synSub synRippleAdd

-- Make a subtractor given an adder.
-- The borrow in and borrow out are complemented.
-- Implemented by negating (complement and increment via ci) second operand
-- and then adding.
synSub :: SynArith -> SynArith
synSub f aid xs ys nbi = do
        nys <- mapM (toS . (aNot aid)) ys
        f aid xs nys nbi

rippleMax :: Int
rippleMax = 8

synXAdd :: SynArith
synXAdd aid xs ys ci =
        (if length xs > rippleMax then
            synCLAAdd
         else
            synRippleAdd)
           aid xs ys ci
synXSub :: SynArith
synXSub = synSub synXAdd

--

type PG = (AExpr, AExpr)

combPG :: AId -> PG -> PG -> S PG
combPG aid (p2, g2) (p1, g1) = do
        po <- toS (aAnd aid p1 p2)
        pg <- toS (aAnd aid p1 g2)
        go <- toS (aOr aid g1 pg)
        return (po, go)

synCLAAdd :: SynArith
synCLAAdd aid xs ys ci = do
        pgs <- zipWithM (hAdd aid) xs ys >>= mapM (toS2 . swap)
        opgs <- scanM (combPG aid) ((aFalse, ci) : pgs)
        let cs = map snd opgs
            ss = map fst pgs
            co = last cs
        return (co, zipWith (aXor aid) ss (init cs))
---

nShiftMux :: Int
nShiftMux = 2

nShiftMuxPow :: Int
nShiftMuxPow = 2^nShiftMux

-- Synthesize a barrel shifter
-- Use one mux layer for every nShiftMux control bits.
synShifter :: AId -> ShiftFun -> [AExpr] -> [AExpr] -> S [AExpr]
synShifter aid shft [] xs = return xs
synShifter aid shft cs xs = do
        let (csn, csr) = splitAt nShiftMux cs
        inp' <- synShifter aid (shft . (* nShiftMuxPow)) csr xs >>= toSs
        shiftLayer aid shft csn inp'

shiftLayer :: AId -> ShiftFun -> [AExpr] -> [AExpr] -> S [AExpr]
shiftLayer aid shft cs xs = do
        let n = length cs
            inps = map (flip shft xs) [0..2^n-1]
        ds <- (synDecode aid cs) >>= toSs
        makeMux aid (zip ds inps)

makeMux :: AId -> [(AExpr, [AExpr])] -> S [AExpr]
makeMux aid cxs = do
            tss <- mapM (\ (c, xs) -> mapM (toS . (aAnd aid) c) xs) cxs
            return (map (aOrs aid) (transpose tss))

type ShiftFun = Int -> [AExpr] -> [AExpr]

permSL :: ShiftFun
permSL  n xs = take (length xs) (replicate n aFalse ++ xs)
permSRL :: ShiftFun
permSRL n xs = take (length xs) (drop n xs ++ repeat aFalse)
permSRA :: ShiftFun
permSRA n xs = take (length xs) (drop n xs ++ repeat (last xs))
-- permRL  n xs = rTake n xs ++ rDrop n xs
-- permRR  n xs = drop n xs ++ take n xs

-----------------------------------------------------------------------------

synMul :: AId -> [AExpr] -> [AExpr] -> S [AExpr]
synMul aid xs ys = do
        let gate :: AExpr -> S [AExpr]
            gate x = toSs (map (aAnd aid x) ys)
            n = length xs
            shft :: Int -> [AExpr] -> [AExpr]
            shft k ys = replicate k aFalse ++ ys ++ replicate (n-k) aFalse
            sumPairwise :: [[AExpr]] -> S [[AExpr]]
            sumPairwise (ys1:ys2:yss) = do
                (_, s) <- synXAdd aid ys1 ys2 aFalse
                s' <- toSs s
                ss <- sumPairwise yss
                return (s':ss)
            sumPairwise yss = return yss
            sumTree :: [[AExpr]] -> S [AExpr]
            sumTree [ys] = return ys
            sumTree yss = sumPairwise yss >>= sumTree
        gyss <- mapM gate xs
        let sgyss = zipWith shft [0..] gyss
        sumTree sgyss

-----------------------------------------------------------------------------

-- scan :: (a->a->a) -> [a] -> [a]
-- scan op xs = f 1 xs
--   where f n xs =
--          case splitAt n xs of
--          (ls, []) -> ls
--          (ls, rs) -> f (2*n) (ls ++ zipWith op xs rs)

scanM :: (a -> a -> S a) -> [a] -> S [a]
scanM op xs = f 1 xs
  where f n xs =
            case splitAt n xs of
            (ls, []) -> return ls
            (ls, rs) -> do
                           ys <- zipWithM op xs rs
                           f (2*n) (ls ++ ys)

swap :: (b, a) -> (a, b)
swap (x, y) = (y, x)
