module AVeriQuirks (aVeriQuirks) where

import Data.List( tails, partition)
import Data.Maybe(catMaybes)
import IntegerUtil(integerAnd, integerOr)
import Util(itos, makePairs)
import PPrint
import IntLit
import ErrorUtil(internalError)
import Position
import Flags(Flags, keepAddSize, removePrimModules, useNegate, readableMux)
import Id
import PreIds(idUnsigned)
import FStringCompat(mkFString)
import Control.Monad(when)
import Control.Monad.State(State, evalState, gets, get, put)
import qualified Data.Map as M
import Prim
import Pragma(defPropsHasNoCSE)
import ASyntax
import ASyntaxUtil
import ForeignFunctions(isAVId, fromAVId)
-- import AOpt(aOptBoolExpr)
import SignalNaming
import Debug.Trace(traceM)



-- =====
-- Naming conventions
aVeriQuirksPref :: String
aVeriQuirksPref = "__q"

debug :: Bool
--debug = True
debug = False

-- =====
-- State for the Monad

data QState = QState {
  -- flags
    qs_keepAddSize   :: Bool,
    qs_rmPrimModules :: Bool,
    qs_useNegate     :: Bool,
    qs_readableMux   :: Bool,
  -- state
    -- unique name generator
    uniqueId :: Integer,
    -- definitions processed so far
    -- at the end, these become the defs of the resulting module
    defs     :: [ADef],
    -- reverse lookup of defs processed or added so far,
    -- to avoid creating new ids for the exprs which already have ids
    -- (defs marked NoCSE are not added to this map)
    rlookup  :: M.Map (AExpr,AType) AId
  }

-- Monad type
type QQState a = State QState a

-- Monad Util
-- Adds a processed def
addDef :: ADef -> QQState ()
addDef newdef@(ADef i t e p) = do
           state <- get
           olddefs <- gets defs
           rlm <- gets rlookup
           let rlm1 = if (defPropsHasNoCSE p)
                      then rlm
                      else M.insert (e,t) i rlm
           when debug $ traceM("VeriQ adding: " ++ ppReadable newdef)
           put state{defs = (newdef:olddefs), rlookup = rlm1 }


-- Generates a new Id from the Expression to give to it
genIdFromAExpr :: AExpr -> QQState AId
genIdFromAExpr expr = do
        state <- get
        oldId <- gets uniqueId
        put state{ uniqueId = oldId + 1 }
        return $ mkId
            noPosition -- XXX aexpr should have an instance of HasPosition
            (mkFString (signalNameFromAExpr expr ++
                        aVeriQuirksPref ++ itos oldId))

-- Add the expression -- really the definition to the monad
addExpr :: AType -> AExpr -> QQState AId
addExpr t e = do
    rlm <- gets rlookup
    case ( M.lookup (e,t) rlm ) of
        Nothing ->
            do
              nid <- genIdFromAExpr e
              addDef (ADef nid t e [])
              return nid
        -- don't create a new id for an expression that already has an id
        Just fid -> return fid


-- Top Level  operations
-- Deal with various quirks in the Verilog syntax & semantics.
aVeriQuirks :: Flags -> ASPackage -> ASPackage
aVeriQuirks flags pkg =
        evalState action initState
  where
        initState =
            QState {
                qs_keepAddSize = keepAddSize flags,
                qs_rmPrimModules = removePrimModules flags,
                qs_useNegate = useNegate flags,
                qs_readableMux = readableMux flags,
                uniqueId = 1,
                defs = [],
                rlookup = M.empty
                   }

        action =
            do
                mapM_ aQDef (aspkg_values pkg)
                is' <- mapM aQInst (aspkg_state_instances pkg)
                fs' <- mapM aQForeignBlock (aspkg_foreign_calls pkg)
                ds' <- gets defs
                return (pkg { aspkg_values = (reverse ds'),
                              aspkg_state_instances = is',
                              aspkg_foreign_calls = fs' })


aQDef :: ADef -> QQState ()
-- Top level case does not need to be pulled out
aQDef (ADef i t e p) = do
    e' <- aQExp True e
    addDef (ADef i t e' p)


aQInst :: AVInst -> QQState (AVInst)
aQInst avi@(AVInst { avi_iargs = args }) = do
  args' <- mapM (aQExp False) args
  return (avi { avi_iargs = args' })


aQForeignBlock :: AForeignBlock -> QQState AForeignBlock
aQForeignBlock (clks, fcalls) = do
  fcalls' <- mapM aQForeignCall fcalls
  fcalls'' <- mapM aQForeignCallAV (catMaybes fcalls')
  return (clks, fcalls'')


aQForeignCall :: AForeignCall -> QQState (Maybe AForeignCall)
aQForeignCall (AForeignCall _ _ (c:es) _ _) | isFalse c = return Nothing
aQForeignCall (AForeignCall id fun es ids resets) = do
  -- turn zero-bit expressions into one-bit expression to pacify Verilog simulators
  let fixupZeroBit e@(ASInt { ae_type = t }) | t == ATBit 0 = e { ae_type = ATBit 1 }
      -- preserve the $unsigned qualifier (and identifier of the underlying object)
      fixupZeroBit e@(AFunCall { ae_type = t, ae_objid = i, ae_args = [arg] })
         | (t == ATBit 0) && (i == (idUnsigned noPosition)) = e { ae_type = ATBit 1, ae_args = [fixupZeroBit arg] }
      -- make all other 0 bits stuff 0
      fixupZeroBit e@(ASAny { ae_type = t }) | t == ATBit 0 = ASInt dummy_id (ATBit 1) (ilSizedBin 1 0)
      fixupZeroBit e | ae_type e == ATBit 0 = ASInt (ae_objid e) (ATBit 1) (ilSizedBin 1 0)
      fixupZeroBit e = e
  es' <- mapM (aQExp False) (map fixupZeroBit es)
  return (Just (AForeignCall id fun es' ids resets))

aQForeignCallAV :: AForeignCall -> QQState AForeignCall
aQForeignCallAV (AForeignCall id fun (cond:es) [d_id] resets) | isAVId id = do
   let id_new  = fromAVId id
       fun_new = getIdBaseString id_new
       aexpr   = ASPort (ATBit 1) d_id -- size is likely wrong but it doesn't affect Verilog
       out     = (AForeignCall id_new fun_new (cond:aexpr:es) [] resets)
   return out
aQForeignCallAV x = return x

-- top argument states if argument is the top expression on the rhs of
-- a ADef and other things as well.
aQExp :: Bool -> AExpr -> QQState AExpr
-- non-constant bit extraction turns into shift and mask
aQExp top (APrim aid t@(ATBit n) PrimExtract [e, h, l])
                | h /= l && not (isConst h && isConst l) =
    let te = aType e
        m = case te of
              (ATBit sz) -> sz
              _ -> internalError "AVeriQuirks.aQExp PrimExtract: unexpected expr type"
        ht = aType h
        -- (e & ~(('1 << 1) << h))
        e1 = APrim aid te PrimAnd [e, mask]
        mask = APrim aid te PrimInv [(APrim aid te PrimSL [maskbase, h])]
        maskbase = ASInt aid te (ilHex (2^m - 2)) -- ('1 << 1)
        -- e1 >> l
        e2 = APrim aid te PrimSRL [e1, l]
        -- extend/truncate e2
        e3 = case (compare m n) of
               GT -> APrim aid t PrimExtract [e2, aSInt ht (n-1), aSInt ht 0]
               LT -> APrim aid t PrimZeroExt [e2]
               EQ -> e2
    in  aQExp top e3

-- probably redundant with IConv
-- e << n && e is 1 bit,  --> n==0 && e ;
aQExp top eee@(APrim aid t@(ATBit 1) op [e1, n]) | op `elem` [PrimSL, PrimSRL] =
    let cond = APrim aid t PrimEQ [n, ASInt aid (ae_type n) (ilDec 0)]
    in aQExp top (APrim aid t PrimBAnd [cond, e1])

-- e << n && e is signed 1 bit,  --> e
aQExp top eee@(APrim aid t@(ATBit 1) PrimSRA [e1, n]) = aQExp top e1

-- Arithmetic (Signed) shift right by constants
aQExp top eee@(APrim aid t@(ATBit n) PrimSRA [e1, ASInt _ _ (IntLit _ _ k)]) =
    let sfted = if (k < n) then
                    APrim aid (ATBit (n-k)) PrimExtract [e1, aSNat (n-1), aSNat k]
                else APrim aid (ATBit 1) PrimExtract [e1, aSNat (n-1), aSNat (n-1)]
    in aQExp top (APrim aid t PrimSignExt [sfted])


-- arithmetic right shift replicates MSB  Need do some shifting and masking
aQExp top (APrim aid t@(ATBit n) PrimSRA [e1,e2]) = do
        let sl = APrim aid (ATBit n) PrimSRL [e1, e2]
            mask = ASInt aid (ATBit n) (ilHex (2^n - 1))
            maskshift = APrim aid (ATBit n) PrimInv [(APrim aid (ATBit n) PrimSRL [mask, e2])]
            msb = APrim aid (ATBit 1) PrimExtract [e1, aSNat (n-1), aSNat (n-1)]
            msbs = APrim aid (ATBit n) PrimSignExt [msb]
            msbmask = APrim aid (ATBit n) PrimAnd [maskshift, msbs]
            sel = APrim aid t PrimOr [sl, msbmask]
        aQExp top sel

-- PrimExtract needs first argument in a variable
aQExp top (APrim aid t PrimExtract [ee,h,l]) = do
    ee' <- mkDefS ee
    h' <- aQExp False h
    l' <- aQExp False l
    return (aExtract aid t ee' h' l')

-- empty sign extends should just be dropped
aQExp top (APrim aid t PrimSignExt [e]) | aSize e == aSize t =
  aQExp top e

-- PrimSignExtend may need its argument in a variable
aQExp top (APrim aid t PrimSignExt [ee]) | aSize ee /= 1 = do
    ee' <- mkDefS ee
    return (APrim aid t PrimSignExt [ee'])

-- some primops need to be at the top of a definition
-- e.g.  case, mux,
aQExp False x@(APrim aid t op es) | topOp op = do
    when debug $ traceM("aQExp topOp True:" ++ ppReadable x)
    es' <- mapM (aQExp False) es
    e <- aQExp True (APrim aid t op es')
    i <- addExpr t e
    return (ASDef t i)

-- noinline functions (that are module instantiations) need to be at the top
aQExp False x@(ANoInlineFunCall t i f es) = do
    es' <- mapM (aQExp False) es
    i <- addExpr t (ANoInlineFunCall t i f es')
    return (ASDef t i)

-- ULT, ULE and EQ can be logically flipped downstream so they do not
-- need additional quirk handling
aQExp top (APrim aid t PrimBNot [e@(APrim _ _ p _)]) | (isSafe p) = do
    e' <- aQExp False e
    return (APrim aid t PrimBNot [e'])
    where isSafe PrimULT = True
          isSafe PrimEQ  = True
          isSafe PrimULE = True
          isSafe PrimEQ3 = True
          isSafe _       = False

aQExp top (APrim aid t PrimNeg es)  = do
    es' <- mapM (aQExp False) es
    un <- gets qs_useNegate
    return (if un then APrim aid t PrimNeg es' else APrim aid t PrimSub (aSInt t 0 : es'))

-- + and - should not have their arguments zero extended
aQExp top (APrim aid t p es) | p == PrimAdd || p == PrimSub = do
    es' <- mapM (aQExp False) es
    keepAddSize <- gets qs_keepAddSize
    let es'' = if keepAddSize then
                let dropzext (APrim aid _ PrimZeroExt [e]) = e
                    dropzext (APrim aid _ PrimConcat [ASInt _ _ (IntLit _ _ 0), e]) = e
                    dropzext e = e
                in  --(if (map dropzext es' /= es') then trace (ppReadable es') else id) $
                    map dropzext es'
               else
                es'
    return (APrim aid t p es'')

-- All multipliers should already be assigned directly to a
-- def, and they should all have output size equal to the
-- sum of the input sizes.  We check those properties here.
aQExp top x@(APrim aid t p es) | p == PrimMul =
    if top
    then if ((aSize t) == (sum (map aSize es)))
         then do es' <- mapM (aQExp False) es
                 return (APrim aid t p es')
         else internalError $ "aQExp: PrimMul result size is ill-typed: " ++ (show x)
    else internalError $ "aQExp: PrimMul does not feed into a def: " ++ (show x)

-- For PrimMux and PrimPriMux operators,
aQExp top x@(APrim aid t p es) | p == PrimMux || p == PrimPriMux = do
    when debug $ traceM("aQExp PrimMux PrimPriMux: " ++ ppReadable x)
    es'           <- mapM (aQExp False) es
    rmPrimModules <- gets qs_rmPrimModules
    readableMux   <- gets qs_readableMux
    case ( rmPrimModules,  readableMux ) of
      (True, False) ->         aQMux aid t p es' -- build AndOr Muxes
      (_, _ )       ->  return (APrim aid t p es')

aQExp top (APrim aid t p es)       = mapM (aQExp False) es >>= return . APrim aid t p
aQExp top (AMethCall t i m es)     = mapM (aQExp False) es >>= return . AMethCall t i m
aQExp top (ANoInlineFunCall t i f es)      = mapM (aQExp False) es >>= return . ANoInlineFunCall t i f
aQExp top (AFunCall t i f isC es)  = mapM (aQExp False) es >>= return . AFunCall t i f isC
aQExp top (ATuple t es)            = do
    es' <- mapM (aQExp False) es
    return (ATuple t es')
aQExp top (ATupleSel t e n)       = do
    e' <- aQExp False e
    return (ATupleSel t e' n)
aQExp top e@(AMethValue {})        = return e
aQExp top e@(ASInt _ _ _)          = return e
aQExp top e@(ASReal _ _ _)         = return e
aQExp top e@(ASStr _ _ _)          = return e
aQExp top e@(ASPort _ _)           = return e
aQExp top e@(ASParam _ _)          = return e
aQExp top e@(ASDef _ _)            = return e
aQExp top e@(ASAny _ _)            = return e
aQExp True  e@(ATaskValue _ _ _ _ _) = return e
aQExp False e@(ATaskValue _ _ _ _ _) = internalError("AVerilog.aQExp: ATaskValue must not be inlined - " ++ ppReadable e)
aQExp _ (ASClock { })              = internalError("AVerilog.aQExp: unexpected clock")
aQExp _ (ASReset { })              = internalError("AVerilog.aQExp: unexpected reset")
aQExp _ (ASInout { })              = internalError("AVerilog.aQExp: unexpected inout")
aQExp _ (AMGate { })               = internalError("AVerilog.aQExp: unexpected gate")

-- these are operations which cannot be nested, since the generated verilog pushed
-- them into a separate always block.
topOp :: PrimOp -> Bool
topOp PrimCase   = True
topOp PrimMux    = True
topOp PrimPriMux = True
topOp _          = False

-- Convert from a Prim{Pri}Mux to a  mux built out of and or logic
-- XXX We should consider optimizing the pred expressions since they can be redundant.
aQMux :: AId -> AType -> PrimOp -> [AExpr] -> QQState AExpr
aQMux aid t@(ATBit n) p as = do
    let (ps, es) = if ( isASAny $ last as)
                   then unzip (makePairs $ init as)
                   else unzip (makePairs as)
        priEnc = map pri . tail . reverse . tails . reverse
        --
        pri :: [AExpr] -> AExpr
        pri [x] = x
        pri (x:xs) = APrim aid aTBool PrimBAnd (x : map aNot xs)
        pri [] = internalError ("AVerilog::aQMux::pri")
        --
        -- bnot x = APrim aid aTBool PrimBNot [x]
    ps'  <- mapM mkDefS ps
    ps'' <- if p == PrimMux then return ps' else {- mapM mkDefS -}  return (priEnc ps')
    let sext e = if n == 1 then e else APrim aid t PrimSignExt [e]
        e = aBitOr aid t [ aBitAnd aid t [sext p, e] | (p, e) <- zip ps'' es ]
    return e
aQMux _ _ _ _  = internalError ("AVerilog::aQMux")


aBitOr :: AId -> AType -> [AExpr] -> AExpr
aBitOr aid t@(ATBit n) es =
    let (cs, xs) = partition isConst es
        one = 2^n-1
        c = foldr (integerOr . getConst one) 0 cs
        aOr' [] = aInt t 0
        aOr' [e] = e
        aOr' es = APrim aid t PrimOr es
    in  if c == one then
            aInt t one
        else if c == 0 then
            aOr' xs
        else
            aOr' (xs ++ [aSInt t c])
aBitOr _ _ _ = internalError ("AVerilog::aOr")

aBitAnd :: AId -> AType -> [AExpr] -> AExpr
aBitAnd aid t@(ATBit n) es =
    let (cs, xs) = partition isConst es
        one = 2^n-1
        c = foldr (integerAnd . getConst 0) one cs
        aAnd' [] = aInt t one
        aAnd' [e] = e
        aAnd' es = APrim aid t PrimAnd es
    in  if c == 0 then
            aInt t 0
        else if c == one then
            aAnd' xs
        else
            aAnd' (xs ++ [aSInt t c])
aBitAnd _ _ _ = internalError ("AVerilog::aAnd")

aInt :: AType -> Integer -> AExpr
aInt t i = aSInt t i
aSInt :: AType -> Integer -> AExpr
aSInt t i = ASInt defaultAId t (ilHex i)

-- mkDefS must return a variable/wire reference
-- even for constants  since Verilog does not allow 7'd8[3:2]
mkDefS :: AExpr -> QQState AExpr
mkDefS e@(AMethCall _ o m []) = return e  -- XXX shouldn't exist
mkDefS e@(AMethValue _ o m)   = return e  -- XXX shouldn't exist
mkDefS e@(ATupleSel _ _ _)  = return e  -- XXX shouldn't exist
mkDefS e@(ASDef {})           = return e
mkDefS e@(ASPort {})          = return e
mkDefS e@(ASParam {})         = return e
mkDefS e@(_)                  = do
    e' <- aQExp True e
    let t = aType e
    i <- addExpr t e'           -- add the new def to the monad
    return (ASDef t i)

-- extracts of v[n:0]  become v
aExtract :: AId -> AType -> AExpr -> AExpr -> AExpr -> AExpr
aExtract _ _ v (ASInt _ _ (IntLit _ _ n')) (ASInt _ _ (IntLit _ _ 0)) | aSize v == n'+1 = v
aExtract aid t v h l = APrim aid t PrimExtract [v,h,l]

aSNat :: Integer -> AExpr
aSNat n = ASInt defaultAId aTNat (ilDec n)

-- utility function to produce a constant
-- turns _ into its first argument
getConst :: Integer -> AExpr -> Integer
getConst d (ASInt _ _ (IntLit _ _ i)) = i
getConst d (ASAny _ _) = d
getConst _ _ = internalError "AVerilog.getConst"
