{-# OPTIONS_GHC -fwarn-name-shadowing -fwarn-missing-signatures #-}

module AOpt(aOpt,
            aOptBoolExpr,
            -- this is needed only because aOptBoolExpr only applies to Bit1
            aBoolSimp,
            -- used by Bluesim backend
            aExpandDynSel, aInsertCaseDef
            -- Used by SERI dump
            ,aOptAPackageLite
            ) where


import Control.Monad(when, foldM, zipWithM)
import Control.Monad.State(State, StateT, evalState, evalStateT, liftIO,
                           gets, get, put)
import Data.List(sortBy, genericLength, sort, transpose, partition, groupBy, nub)
import Util(mapFst)
import qualified Data.Map as M
import qualified Data.Set as S
import Util(allSame, flattenPairs, makePairs, remOrdDup, integerToBits,
            itos, eqSnd, cmpSnd, nubByFst, map_insertManyWith,
            headOrErr, initOrErr, lastOrErr, unconsOrErr)
import IntegerUtil(integerSelect)
import PPrint
import IntLit
import Error(internalError, ErrorHandle)
import Flags(Flags,
             inlineBool,
             optAndOr,
             optATS,
             optAggInline,
             optFinalPass,
             optIfMux,
             optIfMuxSize,
             optMux,
             optMuxExpand,
             optMuxConst,
             optBitConst,
             keepFires,
             optSched,
             optJoinDefs)
import VModInfo(VArgInfo(..), vArgs)
import Position(noPosition)
import FStringCompat(mkFString)
import Id
import ASyntax
import ASyntaxUtil
import AExpand(aExpand, xaSRemoveUnused, xaXExpand, expandAPackage)
import BoolExp
import Prim
import Pragma(defPropsHasNoCSE)
import Data.Maybe(fromMaybe)
import Util(anySame)

import Util(tracep {- , traces -})
import Debug.Trace
import IOUtil(progArgs)

import SAT(SATState, initSATState, checkBiImplication, isConstExpr)

debug :: Bool
debug = "-trace-aopt" `elem` progArgs

debug2 :: Bool
debug2 = debug  && False -- debug

-- =====
-- Naming conventions
aoptPref :: String
aoptPref = "_dm"

-- =====

aOpt :: ErrorHandle -> Flags -> ASPackage -> IO ASPackage
-- we always want to expand even if the opt flag is off.
-- see bug 1069
-- and conversion of array-select to case/if always needs to happen
aOpt errh flags pkg0 | not (optATS flags) =
    let
        keepF = keepFires flags -- F
        inlineB = inlineBool flags -- T

        -- Replace dynamic array select with case expressions.
        -- This needs to be done before aInsertCase, which can merge adjacent
        -- case/if expressions.
        pkg1 = aExpandDynSelASPkg pkg0

        pkg2 = aExpand errh
                   keepF
                   False    -- expnond
                   inlineB  -- expcheap
                   pkg1
    in
        return pkg2
-- when optATS is specified
aOpt errh flags pkg0 = do
    let
        bflags = flagsToBFlags flags

        keepF = keepFires flags -- F
        optsch = optSched flags -- T
        optjoin = optJoinDefs flags -- F  see comments on b1072
        inlineB = inlineBool flags -- T

    when debug $
      traceM ("trace defs, orig : " ++ ppReadable (aspkg_values pkg0))

    let
        -- Replace dynamic array select with case expressions.
        -- This needs to be done before aInsertCase, which can merge adjacent
        -- case/if expressions.
        pkg1A = aExpandDynSelASPkg pkg0

        -- Before any inlining, use aInsertCase to infer case expression.
        -- It only infers in defs, so it needs to be applied before any
        -- inlining.
        -- Note: This can leave unused defs, so we rely on the later opts
        -- to remove unused defs.
        --
        pkg1B =
            let ds = aspkg_values pkg1A
                dmap = M.fromList [ (i, e) | (ADef i _ e _) <- ds ]
                findFn = makeFindFn "AOpt.aInsertCase" dmap
                ds' = map (aInsertCaseDef False findFn) ds
            in  pkg1A { aspkg_values = ds' }

    when debug $
      traceM ("trace defs, post insert-case: " ++ ppReadable (aspkg_values pkg1B))

    let
        -- There are several pass thru aExpand in this function to
        --  give better cleanup and inlining.  This is especially true
        -- after case generation since many signal disappear
        --
        -- expcheap  needed as True here to get aInsertCase to work.
        -- aExpand is needed here after scheduling tsort defs
        --
        pkg2 = aExpand errh
                   keepF
                   False    -- expnond
                   inlineB  -- expcheap
                   pkg1B

        ds = aspkg_values pkg2
        fb = aspkg_foreign_calls pkg2
        ss = aspkg_state_instances pkg2

    when debug $
      traceM ("trace definitions, post expand (ds): " ++ ppReadable ds)

    -- optimize defs with "aOptDefs", then remove defs and expand again
    --
    let (ds1, fb1, ss1) = aOptDefs bflags ds fb ss
    when debug $
      traceM ("trace defs, post aOptDefs (ds1): " ++ ppReadable ds1)
    let pkg3 = pkg2 { aspkg_values = ds1,
                      aspkg_foreign_calls = fb1,
                      aspkg_state_instances = ss1 }
        -- XXX EWC Not sure why optSched is used here ???
        pkg4 = xaSRemoveUnused keepF pkg3
    when debug $
      traceM ("trace defs, post xaSRemoveUnused (ds2): " ++ ppReadable (aspkg_values pkg4))
    let pkg5 = xaXExpand errh
                   keepF
                   optsch  -- expnond
                   False   -- expcheap
                   pkg4

    -- Run thru the SAT solver for and/or optimzation
    --
    when debug $
      traceM ("trace defs, pre aAndOrDefs: " ++ ppReadable (aspkg_values pkg5))
    let str = "aopt_" ++ ppString (aspkg_name pkg0)
    ds2 <- optAndOrDefs str errh flags ( aspkg_values pkg5 )
    when debug $
      traceM ("trace defs, post aAndOrDefs (ds2): " ++ ppReadable ds2)

    -- CSE defs
    --
    let ds3 = joinDefs optjoin ds2
    when debug $
      traceM ("trace defs, post joinDefs (ds3): " ++ ppReadable ds3)
    let pkg6 = pkg5 { aspkg_values = ds3 }

    --
    -- We may want to turn off optsch here, since this undoes the effect of joinDefs
    -- for the simple cases
    let
        pkg7 = xaXExpand errh
                   keepF
                   optsch  -- expnond
                   False   -- expcheap
                   pkg6
        pkg8 = aOptFinalPass flags pkg7
    --
    return pkg8


data BFlags = BFlags  { ao_ifmux        :: Bool,
                        ao_ifmuxsize    :: Integer,
                        ao_mux          :: Bool,
                        ao_muxExpand    :: Bool,
                        ao_muxconst     :: Bool,
                        ao_bitConst     :: Bool,
                        ao_keepfires    :: Bool,
                        ao_keepMethIO   :: Bool,
                        ao_aggInline    :: Bool,
                        ao_ifsToPrimPri :: Bool
                        }

flagsToBFlags :: Flags -> BFlags
flagsToBFlags flags = BFlags {
                              ao_ifmux      = optIfMux flags,     -- T
                              -- double to account for select + argument
                              -- in our mux representation
                              ao_ifmuxsize  = 2 * (optIfMuxSize flags),
                              ao_mux        = optMux flags,       -- T
                              ao_muxExpand  = optMuxExpand flags, -- F
                              ao_muxconst   = optMuxConst flags,  -- T
                              ao_bitConst   = optBitConst flags, -- F
                              --
                              ao_aggInline    = optAggInline flags, -- T
                              ao_keepfires    = keepFires flags, -- False
                              ao_keepMethIO   = keepFires flags,
                              ao_ifsToPrimPri = True
                             }

optFlagsOff :: BFlags -> BFlags
optFlagsOff bflags = bflags {
                             ao_ifmux     = False,
                             ao_mux       = False,
                             ao_muxExpand = False,
                             ao_muxconst  = False,
                             ao_bitConst  = False
                            }

-- only simple optimization, used in optExpr
optExprBFlag ::BFlags
optExprBFlag = BFlags {
  ao_ifmux      = False
  ,ao_ifmuxsize  = 0
  ,ao_mux        = False
  ,ao_muxExpand  = False
  ,ao_muxconst   = False
  ,ao_bitConst   = False
  ,ao_aggInline    = False
  ,ao_keepfires    = False
  ,ao_keepMethIO   = False
  ,ao_ifsToPrimPri = False
                             }
-----

-- Build a state monad containing:
--   the next number for making a unique Id
--   the defs
--   a map of Ids to their expressions (hopefully consistent with the defs)

-- The reason for this is that some optimizations may create new defs.
-- For example, an expression which is turned into a concatenation of
-- its the extractions of each bit (for simplifying bit-wise ops on
-- constants) might call mkDefS, which defines a name for each piece
-- to be concatenated.  By storing those in the monad, we need not
-- plumb the new definitions around.

type DefMap = (M.Map AId AExpr)

type UseMap = (M.Map AId Int)

data OState = OState { o_nextid :: Integer,
                       o_defs   :: [ADef],
                       o_defmap :: DefMap,
                       o_usemap :: UseMap
                     }

-- start with Id 1, no defs, and an uninitialized map
initOState :: OState
initOState = OState { o_nextid = 1,
                      o_defs   = [],
                      o_defmap = M.empty,
                      o_usemap = M.empty
                    }

type O a = State OState a


-- adding a def does affect the map
addDef ::  ADef -> O ()
addDef d@(ADef aid t e _) = do
  s <- get
  let uses = (aid,0) : map (\i -> (i,1)) (aVars e)
  put s { o_defs   = d:o_defs s,
          o_defmap = M.insert aid e (o_defmap s),
          o_usemap = map_insertManyWith (+) uses (o_usemap s)
        }

-- retrieve the defs (in order they were added)
getDefs :: O [ADef]
getDefs = do
  s <- get
  return $ reverse $ o_defs s

-- clear out the defs from the monad
clearDefs :: O ()
clearDefs = do
  s <- get
  put s { o_defmap = M.empty, o_defs = [], o_usemap = M.empty }

-- make a new name with the next uniquifier appended to the prefix ("_dm")
-- XX only used with the mux opt which is turned off!
newName :: O AId
newName = do
  s <- get
  put s { o_nextid = 1 + o_nextid s }
  let
      new_name = mkFString (aoptPref ++ itos (o_nextid s))
      new_id = setBadId (mkId noPosition new_name)
  return new_id


-- looks upa given definition
lookupDef :: AId -> O ( Maybe AExpr )
lookupDef aid = gets o_defmap >>= return . M.lookup aid

-- returns a function on the given state:
--   given an Id, look it up in the map, and return its expression,
--   else (if not there) look it up in the defs
findDef :: O (AId -> AExpr)
findDef = do
  dmap <- gets o_defmap
  return $ makeFindFn "AOpt.findDef" dmap

makeFindFn :: String -> DefMap -> (AId -> AExpr)
makeFindFn str dmap v =
  case M.lookup v dmap of
    Just e -> e
    Nothing -> internalError(str ++ " inconsistent: " ++
                             ppReadable (v, M.toList dmap))


-- Start the map off with the non-def uses
setNonDefUses :: [AVInst] -> [AForeignBlock] -> O ()
setNonDefUses ss fs = do
  let vuses = aVars ss
  let fuses = aVars fs
  let uses = map (\i -> (i,1)) (vuses ++ fuses)
  let newMap = M.fromListWith (+) uses
  s <- get
  put s { o_usemap = newMap }

findUse :: O (AId -> Bool)
findUse = do
  umap <- gets o_usemap
  return
    (\ v -> case M.lookup v umap of
              Just i  -> (i == 1)
              Nothing -> internalError("AOpt.findUse inconsistent" ++ ppReadable (v, M.toList umap))
    )

{-
traceUses :: O ()
traceUses = do
  umap <- gets o_usemap
  defs <- gets o_defs
  traceM ("uses = " ++ ppReadable (M.toList umap))
  traceM ("defs = " ++ ppReadable (map adef_objid defs))
-}
-----

-- keep expanding an expression until it is not a variable reference
-- This is used for inferring case statements, so the find function
-- returns the pre-optimized def
expandVarRef :: (AId -> AExpr) -> AExpr -> AExpr
expandVarRef findf (ASDef { ae_objid = aid }) = expandVarRef findf (findf aid)
expandVarRef _ e = e

-- only expand if the def is used once
-- This is used with a post-optimization find function, since there is no
-- use map accompanying the pre-optimization defs.
expandUniqueVarRef :: (AId -> Bool) -> (AId -> AExpr) -> AExpr -> AExpr
expandUniqueVarRef isUnique findf e@(ASDef { ae_objid = aid })
        | (isUnique aid) = expandUniqueVarRef isUnique findf (findf aid)
--        | otherwise = trace ("choosing not to expand " ++ ppReadable aid) $ e
expandUniqueVarRef _ _ e = e

-----

-- Top-level optimization function over all local defs
--   calls aOptDef and aMuxOptDef on each def
aOptDefs :: BFlags -> [ADef] -> [AForeignBlock] -> [AVInst] -> ([ADef],[AForeignBlock],[AVInst])
aOptDefs bflgs ds fblocks ss = (evalState optf initOState)
  where optf :: O ( [ADef], [AForeignBlock], [AVInst] )
        optf = do
            --traceM ("FF " ++ ppReadable ds)
            setNonDefUses ss fblocks
            -- and various prim opt  aPrim (incld some flattening / joining of nested muxes
            mapM_ (aOptDef bflgs) ds
            fb1 <- mapM (aOptForeignBlock bflgs) fblocks
            ds' <- getDefs
            when debug2 $ traceM ("trace post aoptdef in aoptDefs : " ++ ppReadable ds' )
            clearDefs
            setNonDefUses ss fb1
            -- Do the mux optimization
            mapM_ (aMuxOptDef bflgs) ds'
            fb2 <- mapM (aMuxOptForeign bflgs) fb1
            ss1 <- mapM (aOptInstDefs bflgs) ss
            newdefs <- getDefs
            return (newdefs,fb2,ss1)

aOptInstDefs :: BFlags -> AVInst -> O AVInst
aOptInstDefs bflgs inst =
    do
      newArgs <- zipWithM (aOptInstArg bflgs) (vArgs (avi_vmi inst)) (avi_iargs inst)
      return inst {avi_iargs = newArgs}

aOptInstArg :: BFlags -> VArgInfo -> AExpr -> O AExpr
aOptInstArg bflgs (Param _) =
    -- We used to do no optimization on parameters, but we should at least
    -- do constant propagation because don't-care values might have been
    -- replaced with constants; we just need to avoid any opts that might
    -- create defs, so we disable those
    aExp (bflgs { ao_ifmux = False, ao_bitConst = False })
aOptInstArg bflgs _ = aExp bflgs


-- Top-level optimization
-- If any local id has the same definition (expr) as a previously
-- encountered id, then change the def of the second occurrence to be
-- just a reference to the first.
joinDefs :: Bool -> [ADef] -> [ADef]
joinDefs False ds = ds
joinDefs True dsx = reverse (snd (foldl add (M.empty, []) dsx))
  where add :: (M.Map AExpr ADef, [ADef]) -> ADef -> (M.Map AExpr ADef,[ADef])
        add (m, ds) d@(ADef _ _ (ASInt _ _ _) _) = (m, d:ds)
        add (m, ds) d@(ADef _ _ (ASDef _ _) _)   = (m, d:ds)
        add (m, ds) d@(ADef _ _ (ASStr _ _ _) _) = (m, d:ds)
        add (m, ds) d@(ADef _ _ (ASPort _ _) _)  = (m, d:ds)
        add (m, ds) d@(ADef _ _ (ASParam _ _) _) = (m, d:ds)
        add (m, ds) d@(ADef _ _ (ASAny _ _) _)   = (m, d:ds)
        add (m, ds) d@(ADef ie _ e props)            =
                case M.lookup e m of
                Nothing
                    | hasIdProp ie IdP_enable  -> (m, d:ds)
                    | defPropsHasNoCSE props   -> (m, d:ds)
                    | otherwise                -> (M.insert e d m, d:ds)
                Just (ADef i t _ p) -> -- traces ("adding simple assignment: " ++ ppReadable (ie,i)) $
                                     (m, (ADef ie t (ASDef t i) p) : ds)

-- if the expression is a primitive with 1-bit type, optimize it as
-- a boolean expression
-- (this top-level entry point is called by AVeriQuirks and Synthesize)
aOptBoolExpr :: AExpr -> AExpr
aOptBoolExpr (APrim aid t p es) = aPrimBool aid t p es
aOptBoolExpr e = e

-- aOptDefs does the aInsertCase optimization over all defs before
-- calling aOptDef, so there is no need to call aInsertCase here.
-- Note: When aInsertCase was called here, it had to be called first,
--   because it converts if-then-else to case-statement when possible.
--   Any remaining if-then-else is converted to a mux by aExp.  aExp also
--   optimizes the resulting case-statement by filling it out.  For both
--   reasons, aInsertCase must come before aExp.
aOptDef :: BFlags -> ADef -> O ()
-- inline ASDef references more eagerly than aExp
-- (but don't inline ATaskValue or foreign AFunCall,
-- which need to keep their def names)
aOptDef bflgs def@(ADef i t rdef@(ASDef rt aid) ps) = do
    mredirect <- lookupDef aid
    -- traceM( "aoptdef redirect: " ++ ppReadable rdef)
    case (mredirect) of
        Nothing ->
            internalError ("Aopt::aOptDef lookup failed: " ++ ppReadable def)
        Just (ATaskValue {}) -> aOptDef_dflt bflgs def  -- don't redirect
        Just (AFunCall { ae_isC = True }) -> aOptDef_dflt bflgs def  -- don't redirect
        Just rdef_expr -> addDef (ADef i t rdef_expr ps)
aOptDef bflgs def = aOptDef_dflt bflgs def

-- the default case for aOptDef (shared between the two branches above)
aOptDef_dflt :: BFlags -> ADef -> O ()
aOptDef_dflt bflgs def@(ADef i t e p) = do
    --e' <- aInsertCase e
    --when debug2 $ traceM( "aOptDef: IC: " ++ ppReadable e' )
    e'' <- aExp bflgs e
    when debug2 $ traceM( "aOptDef: " ++ ppReadable def ++
                          "result : " ++ ppReadable e'' )
    addDef (ADef i t e'' p)

aOptForeignBlock :: BFlags -> AForeignBlock -> O AForeignBlock
aOptForeignBlock bflgs (cs,afcs) = do
  afcs1 <- mapM aOptForeignCalls afcs
  return (cs,afcs1)
      where aOptForeignCalls :: AForeignCall -> O AForeignCall
            aOptForeignCalls afc = do
              args1 <- mapM (aExp bflgs) (afc_args afc)
              rsts1 <- mapM (aExp bflgs) (afc_resets afc)
              when debug2 $ traceM("aOptForeignBlock 0 : " ++ ppReadable (afc_args afc))
              when debug2 $ traceM("aOptForeignBlock 1 : " ++ ppReadable args1)
              return afc { afc_args = args1,
                           afc_resets = rsts1 }

aMuxOptForeign :: BFlags -> AForeignBlock -> O AForeignBlock
aMuxOptForeign bflgs  (cs,afcs) = do
  afcs1 <- mapM aMuxOptForeignCalls afcs
  return (cs,afcs1)
      where aMuxOptForeignCalls :: AForeignCall -> O AForeignCall
            aMuxOptForeignCalls afc = do
              args0 <- mapM (aMuxOptConst bflgs) (afc_args afc)
              args1 <- mapM (aMuxOpt bflgs) args0
              rsts0 <- mapM (aMuxOptConst bflgs) (afc_resets afc)
              rsts1 <- mapM (aMuxOpt bflgs) rsts0
              when debug2 $ traceM("aMuxOptForeignBlock 0 : " ++ ppReadable (afc_args afc))
              when debug2 $ traceM("aMuxOptForeignBlock 1 : " ++ ppReadable args1)
              return afc { afc_args = args1,
                           afc_resets = rsts1 }

aMuxOptDef :: BFlags -> ADef -> O ()
aMuxOptDef bflgs (ADef i t e p) = do
    e1 <- aMuxOptConst bflgs e
    e2 <- aMuxOpt bflgs e1
    addDef (ADef i t e2 p)


type OptFunction = BFlags -> AId -> AType -> PrimOp -> [AExpr] ->  O AExpr

-- A general function to optimize down a tree.
aOptTree :: BFlags -> (OptFunction) -> AExpr -> O AExpr
aOptTree bflgs ofunc (APrim aid t p es)   = mapM (aOptTree bflgs ofunc) es >>= ofunc bflgs aid t p
aOptTree bflgs ofunc (AMethCall t i m es) = mapM (aOptTree bflgs ofunc) es >>= return . AMethCall t i m
aOptTree bflgs ofunc (ANoInlineFunCall t i f es)  = mapM (aOptTree bflgs ofunc) es >>= return . ANoInlineFunCall t i f
aOptTree bflgs ofunc (AFunCall t i f isC es)  = mapM (aOptTree bflgs ofunc) es >>= return . AFunCall t i f isC
aOptTree _ _ e  = return e

aMuxOpt :: BFlags -> AExpr -> O AExpr
aMuxOpt bflgs aexpr = aOptTree bflgs aMuxOptPrim aexpr
    where
      aMuxOptPrim :: BFlags -> AId -> AType -> PrimOp -> [AExpr] ->  O AExpr
      aMuxOptPrim bflags aid t p es | p == PrimMux || p == PrimPriMux = muxOpt bflags aid t p es
      aMuxOptPrim bflags aid t p es                                   = return $ APrim aid t p es


-- Wrapper for mux constanst
aMuxOptConst :: BFlags -> AExpr -> O AExpr
aMuxOptConst bflgs aexpr = aOptTree bflgs aMuxOptC aexpr
    where
      aMuxOptC :: BFlags -> AId -> AType -> PrimOp -> [AExpr] ->  O AExpr
      aMuxOptC bflags aid t p es | p == PrimMux || p == PrimPriMux = muxOptConst bflags aid t p es
      aMuxOptC bflags aid t p es                                   = return $ APrim aid t p es

{-aMuxOpt bflgs (APrim aid t p es) = mapM (aMuxOpt bflgs) es >>= aMuxOptPrim bflgs aid t p
aMuxOpt bflgs (AMethCall t i m es) = mapM (aMuxOpt bflgs) es >>= return . AMethCall t i m
aMuxOpt bflgs (ANoInlineFunCall t i f es) = mapM (aMuxOpt bflgs) es >>= return . ANoInlineFunCall t i f
aMuxOpt bflgs (AFunCall t i f isC es) = mapM (aMuxOpt bflgs) es >>= return . AFunCall t i f isC
aMuxOpt bflgs e@(_) = return e
-}


-----

aExpandDynSelASPkg :: ASPackage -> ASPackage
aExpandDynSelASPkg pkg0 =
    let ds = aspkg_values pkg0
        dmap = M.fromList [ (i, e) | (ADef i _ e _) <- ds ]
        findFn = makeFindFn "AOpt.aExpandDynSel" dmap
    in  aExpandDynSel False findFn pkg0

-- entry point for replacing dynamic select with case expressions
-- (or if-expressions, for Strings, which Verilog can't support as case)
--
aExpandDynSel :: (AExprs a) => Bool -> (AId -> AExpr) -> a -> a
aExpandDynSel stringOK findFn = mapAExprs expDynSel
  where
        expDynSel (APrim sel_i sel_ty PrimArrayDynSelect [arr_e, idx_e]) =
           case arr_e of
             ASDef _ i ->
                 let arr_e' = findFn i
                 in  expDynSel
                         (APrim sel_i sel_ty PrimArrayDynSelect [arr_e', idx_e])
             APrim arr_i arr_ty PrimBuildArray elem_es ->
               let idx_ty = ae_type idx_e
                   max_idx = case idx_ty of
                               ATBit sz -> (2^sz) - 1
                               _ -> internalError ("aExpandDynSel: idx_ty")
                   -- number of arms is the min of the elems and the max index
                   arms = zip [0..max_idx] elem_es
                   -- make the last string be the default, if necessary
                   (arms_init, arms_last) =
                       (initOrErr "aExpandDynSel: init" arms,
                        lastOrErr "aExpandDynSel: last" arms)
                   mkLit n = ASInt defaultAId idx_ty (ilDec n)
                   mkCaseArm (n, e) = (mkLit n, e)
               in
                 if (isStringType sel_ty) && (not stringOK)
                 then
                   -- Verilog has to use if expressions for non-bit types
                   let foldFn (n, thn) els =
                         let cond = APrim sel_i aTBool PrimEQ [idx_e, mkLit n]
                         in  APrim sel_i sel_ty PrimIf [cond, thn, els]
                   in  foldr foldFn (snd arms_last) arms_init
                 else if (isStringType sel_ty)
                 then
                   -- We still want to avoid creating an ASAny of type String
                   -- so for now use the last string as the default
                   let case_arms = map mkCaseArm arms_init
                       default_e = snd arms_last
                   in  APrim sel_i sel_ty PrimCase
                          (idx_e : default_e : flattenPairs case_arms)
                 else
                   let case_arms = map mkCaseArm arms
                       default_e = ASAny (getArrayElemType arr_ty) Nothing
                   in  APrim sel_i sel_ty PrimCase
                          (idx_e : default_e : flattenPairs case_arms)
             _ -> internalError ("aExpandDynSel: unexpected array: " ++
                                 ppReadable arr_e)
        expDynSel e = e


-----

-- entry point for optimizing nested if-expressions in an expr,
-- converting them to case-expressions in some situations.
-- * nested ifs of 4 or more arms (including default) are converted
-- * XXX could check for completeness here?
-- * Note: this can inline references to other defs, to build the case
--
aInsertCaseDef :: Bool -> (AId -> AExpr) -> ADef -> ADef
aInsertCaseDef stringOK findFn (ADef i t e p) =
    ADef i t (aInsertCase stringOK findFn e) p

aInsertCase :: Bool -> (AId -> AExpr) -> AExpr -> AExpr
aInsertCase stringOK findFn (APrim i t p es) =
    let es' = map (aInsertCase stringOK findFn) es
    in  aPrimInsertCase stringOK findFn i t p es'
aInsertCase stringOK findFn (AMethCall t i m es) =
    let es' = map (aInsertCase stringOK findFn) es
    in  AMethCall t i m es'
aInsertCase stringOK findFn (AFunCall t i f isC es) =
    let es' = map (aInsertCase stringOK findFn) es
    in  AFunCall t i f isC es'
aInsertCase _ _ e = e

-- Convert any nested if-expressions that are checking the value of
-- one variable (e.g. "if (v == 1) else if (v == 2) ...") into a case
-- expression.  Allows arms such as "if (v == 3) || (v == 5)", but
-- they become separate arms in the case statement.
aPrimInsertCase :: Bool -> (AId -> AExpr) ->
                   AId -> AType -> PrimOp -> [AExpr] -> AExpr
aPrimInsertCase stringOK findFn aid t PrimIf es@[cond, _, _]
  | stringOK || not (isStringType t) =
    -- if the condition is of the form "(v == c) || (v2 == c2) || ...",
    -- then this will be Just [(v,c), (v2,c2), ...]
    let mcs = getConsts findFn (const True) cond
        res = case mcs of
                -- if all the v's are the same
                Just cs@((v,_):_) | allSame (map fst cs) ->
                    -- collect the ifs,
                    -- if there are any nested, convert to case
                    let (ces, d) = collIf findFn v [] (APrim aid t PrimIf es)
                        -- aPrim will check this again
                        -- but we do it here for the Bluesim backend
                        ces' = rmDupsInCasePairs ces
                    in  if length ces > 1
                        then APrim aid t PrimCase (v:d:flattenPairs ces')
                        else APrim aid t PrimIf es
                _ -> APrim aid t PrimIf es
    in  tracep debug2 ("aPrimInsertCase: " ++ ppReadable es) $
        tracep debug2 ("aPrimInsertCase: result: " ++ ppReadable res) $
        res
aPrimInsertCase stringOK findFn aid t p es = APrim aid t p es

-----

-- entry point for optimizing expressions
-- Note: this can inline if it reveals nested muxes that can be merged
aExp :: BFlags -> AExpr -> O AExpr
--
--
aExp bflags (APrim aid t p es)   = mapM (aExp bflags) es >>= aPrim bflags aid t p
aExp bflags (AMethCall t i m es) = mapM (aExp bflags) es >>= return . AMethCall t i m
aExp bflags (AFunCall t i f isC es)  = mapM (aExp bflags) es >>= return . AFunCall t i f isC
--
-- One might consider not passing up constants and simple definitions through
-- keep signals such as CAN/WILL Fire and method ids, but that leads to more disparity
-- about signal names and less optimization by bsc. E.g.  it is better to have a case (state)
-- then to have case (1'b1)  CAN_FIRE_R1: etc.
--  here we do an aggressive inlining of signals and constants.
aExp bflags etop@(ASDef t aid) =
    do mexpr <- lookupDef aid
       let e = fromMaybe (internalError("AOpt::aExp ADef lookup failed " ++ ppReadable aid)) mexpr
           aggInline = ao_aggInline bflags
       return $
         case (aggInline, e ) of
           (True,  el@(APrim _ _ PrimExtract [ _, (ASInt {} ), (ASInt {} ) ]))
                                        -> el
           (True,  el@(AMethValue {} )) -> el
           (True,  el@(ASPort {} ))     -> el
           (True,  el@(ASParam {} ))    -> el
           (True,  el@(ASDef {} ))      -> el
           (_,     el@(ASInt {} ))      -> el
           (_,     el@(ASStr {} ))      -> el
           -- Do not inline in other cases.
           -- In particular, ATaskValue must stay toplevel,
           -- with the same def name.
           _                            -> etop

aExp bflags etop@(ASPort t aid)  = -- port can be constant,  check here
    do me <- lookupDef aid
       return $ case me of
                  Just ( el@(ASInt {} )) -> el -- push through consts and other defs
                  _                      -> etop
aExp bflags e@(_)                = return e


-- various optimizations
-- single level only aExp traverses nested expressions
aPrim :: BFlags -> AId -> AType -> PrimOp -> [AExpr] -> O AExpr

-- if (!c) tt ee  -->  if (c) ee tt
aPrim bflags aid t PrimIf [APrim _ _ PrimBNot [c], tt, ee]
    = aPrim bflags aid t PrimIf [c, ee, tt]

-- if True tt ee --> tt
aPrim bflags aid t PrimIf [cnd, tt,ee]  | isTrue cnd = return tt

-- if False tt ee --> ee
aPrim bflags aid t PrimIf [cnd, tt,ee]  | isFalse cnd = return ee

-- if _ e e --> e
aPrim bflags aid t PrimIf [_,tt,ee] | (tt == ee) = return ee

-- if x then !y else y  -->  x ^ y
aPrim bflags aid t@(ATBit 1) PrimIf [cnd, thn, els]
    | thn == sAPrim t PrimBNot [els]
    = aPrim bflags aid t PrimXor [cnd, els]

-- if x then y else !y  -->  !(x ^ y)
aPrim bflags aid t@(ATBit 1) PrimIf [cnd, thn, els]
    | els == sAPrim t PrimBNot [thn]
    = aPrim bflags aid t PrimBNot [sAPrim t PrimXor [cnd, thn]]

-- look for Trues and Falses in And and Or Expressions
aPrim bflags aid t@(ATBit 1) op es
    | (op == PrimAnd || op == PrimBAnd ) && any isFalse es = return aFalse
aPrim bflags aid t@(ATBit 1) op es
    | (op == PrimAnd || op == PrimBAnd ) && any isTrue es
      = do
           let es1 = filter (not . isTrue ) es
           case es1 of
                []   -> return aTrue
                [ex] -> return ex
                exs  -> aPrim bflags aid t op $ nub exs

-- repeat this one for PrimOr
aPrim bflags aid t@(ATBit 1) op es
    | (op == PrimOr || op == PrimBOr ) && any isTrue es = return aTrue
aPrim bflags aid t@(ATBit 1) op es
    | (op == PrimOr || op == PrimBOr ) && any isFalse es
      = do
           let es1 = filter (not . isFalse ) es
           case es1 of
                []   -> return aFalse
                [ex] -> return ex
                exs  -> aPrim bflags aid t op $ nub exs

aPrim bflags aid t@(ATBit 1) op es
    | (op == PrimAnd || op == PrimBAnd || op == PrimOr || op == PrimBOr ) && anySame es = aPrim bflags aid t op (nub es)

-- turn if into a mux
-- (if optIfMux flag is True)
-- Note: this can inline
aPrim bflags aid t PrimIf [cnd, x, y]  | ao_ifmux bflags && not (isStringType t) = do
    let muxSize = ao_ifmuxsize bflags
    c' <- mkDefS cnd
    findD <- findDef
    findU <- findUse
    let -- if inlining reveals an expression that's a mux return it, else
        -- returns the original expression
        usePrimPri = ao_ifsToPrimPri bflags
        op = if (usePrimPri) then PrimPriMux else PrimMux
        --
        inlineMux :: AExpr -> O AExpr
        inlineMux e@(ASDef { }) = do
            let e' = (expandUniqueVarRef findU findD e)
            case (e') of
              (APrim _ _ opx es) | opx == op &&
                                   genericLength es < muxSize -> return e'
              _ -> return e
        inlineMux e = return e
        --
    x' <- inlineMux x
    y' <- inlineMux y
    let notc' = aNot c'
        otherCond = if ( usePrimPri) then aTrue else notc'
        -- if the underlying expression is a mux, join them
        addToMux :: AExpr -> AExpr -> [AExpr]
        addToMux c (APrim _ _ opx es) | opx == op =
            flattenPairs $ nubByFst (mapFst (aAnd c) (makePairs es))
        addToMux c e = [c, e]
    let es' = addToMux c' x' ++ addToMux otherCond y'
    when debug2 $ traceM("optIfMux size: " ++ show (length es'))
    aPrim bflags aid t op es'


-- fill case expressions or optimize
-- is
-- Optimize if the selection is a const, and all arm conditions are const
aPrim _ aid t PrimCase args@(v:d:ces)
    | (isConst v) && all (isConst . fst) armpairs =
        do when debug2 $ traceM ("aPrim PrimCase 1: " ++ ppReadable args )
           return $ fromMaybe d (lookup v armpairs)
    where armpairs = makePairs ces

--- fill case expressions
aPrim _ aid t PrimCase (v:d:ces) =
    do
      let arms = rmDupsInCasePairs (makePairs ces)
      let ces' = flattenPairs (complete (aType v) d arms)
      when debug2 $ traceM ("APrim PrimCase2: " ++ ppReadable aid ++ " "
                            ++ ppReadable (makePairs ces)
                            ++ "\n rmdups: " ++ ppReadable arms
                            ++ "\n result: " ++ ppReadable (makePairs ces'))
      return $ APrim aid t PrimCase (v:d:ces')

-- do constant propagation for PrimArrayDynSelect
-- which may accidentally exist because of a don't-care value,
-- whose value was eventually picked
aPrim _ sel_i sel_ty PrimArrayDynSelect
              args@[APrim arr_i arr_ty PrimBuildArray elem_es,
                    ASInt _ _ (IntLit { ilValue = idx })] =
    do when debug2 $ traceM ("aPrim PrimDynSelect: " ++ ppReadable args)
       let dflt = if (isStringType sel_ty)
                  then lastOrErr "aPrim: empty array" elem_es
                  else ASAny sel_ty Nothing
           idx' = fromInteger idx
           res = if (idx' >= length elem_es)
                 then dflt
                 else elem_es!!idx'
       return res

-- flatten concatenation
aPrim _ aid t PrimConcat es = return $ aConcat es

-- optimize bitwise ops with constants
-- (if optBitConst flag is True)
aPrim bflags aid t@(ATBit n) p exs
    | ao_bitConst bflags &&  bitwise p && any isInt exs = do
    -- trace (ppReadable (APrim _ t p es)) $ return ()
    let mkBit (ASInt _ _ (IntLit { ilValue = i })) =
                return (integerToAExprs n i) -- fast special case
        mkBit e = do
            e' <- mkDefS e
            getf <- findDef
            let err = internalError "AOpt.aPrim.mkBit"
                e'' = APrim aid err PrimConcat (aFlattenConc True getf e')
            return [ aSelect e'' i 1 | i <- [n-1,n-2..0] ]
        mkCol es = aPrimBool aid aTBool (boolOp p) es
    ess <- mapM mkBit exs
    aPrim bflags aid t PrimConcat (map mkCol (transpose ess))

-- handle consts -- these occur from rwire inlining
aPrim bflags aid dty op [x,y]
      | op == PrimEQ && any isASAny [x,y] = return aTrue
      -- Semantically, this seems correct for Verilog,
      -- but it is more predictable to retain === and
      -- let the chips (e.g. -unspecified-to) fall where they may.
      -- | op == PrimEQ3 && any isASAny [x,y] = return aFalse
      | op `elem` [ PrimEQ, PrimEQ3 ]  && all isConst [x,y] =
          return $ if (x == y) then aTrue else aFalse

-- extract of a const can be simplified
aPrim bflags aid dty PrimExtract [e@(ASInt _ _ c), h@(ASInt _ _ hi), l@(ASInt _ _ lo)]  = do
    let
        vhi = ilValue hi
        vlo = ilValue lo
        finalSize = vhi - vlo + 1
    return (ASInt aid (ATBit finalSize) (truncateInteger (ilValue c) vhi vlo))

-- Always do bool simplification for 1 bit opt!?
aPrim _ aid t p es = return $ aPrimBool aid t p es

----------------------------
-- final pass optimization.
-- unnest flatten expressions e.g. (A & B) & C  ==>  A & B & C
-- concats are handled separately, since bits can be merged as well.
aOptFinalPass :: (AExprs a) => Flags -> a -> a
aOptFinalPass flags p | optFinalPass flags == False = p
                     | otherwise = mapAExprs flattenExprs p
    where flattenExprs :: AExpr -> AExpr
          flattenExprs  (APrim i e op es) | op `elem` communitiveOps =
                                              let es' = mapAExprs flattenExprs es
                                              in APrim i e op (concatMap (unnest op) es')
                                          | op == PrimConcat =
                                              aConcat (mapAExprs flattenExprs es)
                                          | otherwise =
                                              APrim i e op (mapAExprs flattenExprs es)
          flattenExprs   e = e
          --
          communitiveOps = [PrimAdd, PrimOr, PrimBOr, PrimBAnd, PrimAnd, PrimXor]
          --
          unnest :: PrimOp -> AExpr -> [AExpr]
          unnest op1 (APrim i e op es) | op == op1 = es
          unnest _ e = [e]


truncateInteger :: Integer -> Integer -> Integer -> IntLit
truncateInteger value hi lo =
    ilBin $ (value `div` (pow lo)) `mod` (pow (hi - lo + 1))
  where pow n = 2 ^ n

-- If the expression is a 1-bit type, then try to simplify it as a
-- boolean expression (using aBoolSimp)
aPrimBool :: AId -> AType -> PrimOp -> [AExpr] -> AExpr
aPrimBool aid t@(ATBit 1) p es = aBoolSimp (APrim aid t p es)
aPrimBool aid t p es = APrim aid t p es

bitwise :: PrimOp -> Bool
bitwise PrimAnd = True
bitwise PrimOr  = True
bitwise PrimXor = True
bitwise _       = False

boolOp :: PrimOp -> PrimOp
boolOp PrimAnd = PrimBAnd
boolOp PrimOr  = PrimBOr
boolOp PrimXor = PrimXor
boolOp _ = internalError( "AOpt::boolOp" )

-----

-- This may have started out as "make Definition Simple".
-- It takes an expression and returns the expression in a simplified
-- form, possibly having added new variable declarations to the monad
-- (to replace non-simple parts of the expression with variable
-- references.)
-- Currently, the only simplification it does is to declare a new
-- definition for any piece of a concatenation which is not already
-- simple (a const or a variable).  These new definitions are added
-- to the monad (thus the use of the monad -- to avoid plumbing new
-- defs around).
mkDefS :: AExpr -> O AExpr
mkDefS e@(AMethCall _ o m []) = return e
-- concatenation and selection don't need CSE since they don't compute
mkDefS (APrim aid t PrimConcat es) = do
    es' <- mapM mkDefS es
    return $ APrim aid t PrimConcat es'
--- mkDefS (APrim _ t PrimExtract [e, h@(ASInt _ _ _), l@(ASInt _ _ _)]) = do
---     e' <- mkDefS e
---     return $ APrim _ t PrimExtract [e', h, l]
-- don't declare a new signal for expressions which are already simple
mkDefS e | isASimple e = return e
mkDefS e = do
    i <- newName
    let t = aType e
    addDef (ADef i t e [])
    return (ASDef t i)

-----

sAPrim :: AType -> PrimOp -> [AExpr] -> AExpr
sAPrim t op es = APrim defaultAId t op es

isInt :: AExpr -> Bool
isInt (ASInt _ _ _) = True
isInt _ = False

aBool  :: Bool -> AExpr
aBool b = aSBool b

-----

-- Collect nested if's and case's
-- Given a find function (for following defs),
-- and a variable (v) that the first if expression is conditional on,
-- and the constant expressions found so far (ces):
-- if the else clause is an if expression on the same variable
-- (according to getConsts), then add those constants to ces and
-- recurse on the else clause of the next level.
-- If a case statement on the same variable is found, add the ces to
-- those found in the case.
-- If anything else is found, return the ces so far.
-- The second item (d) returned is the final else expression (the default).
-- Note that "if (x == 1) || (x == 2)" generates two entries in "ces"
-- (two arms in the case).
--
-- Note: The "find" function probably needs to be a lookup of
-- pre-optimization values.  Because aPrimInsertCase is called on each opt,
-- interleaved with aOptDef, and so each if-else will be converted to
-- PrimCase and then aOptDef will fill out this case.  This does not seem
-- to be too much extra work; but if one wants to save work, maybe we can
-- map aPrimInsertCase over all the defs first, then call aOptDef ...
-- perhaps even removing any defs that were inlined away by aPrimInsertCase
-- before mapping aOptDef.
--
collIf :: (AId -> AExpr) -> AExpr -> [(AExpr, AExpr)] -> AExpr ->
          ([(AExpr, AExpr)], AExpr)
collIf findf v ces d =
    let -- this is either the original expr or an expanded variable ref
        d' = expandVarRef findf d
    in
        case (collIfPrim findf v ces d') of
            Just res -> res
            Nothing  -> (reverse ces, d)

-- This does the real work.
-- It returns (Just result) if optimization was possible
collIfPrim :: (AId -> AExpr) -> AExpr -> [(AExpr, AExpr)] -> AExpr -> Maybe ([(AExpr, AExpr)], AExpr)
collIfPrim findf v ces (APrim _ _ PrimIf [_, t, e]) | t == e =
        Just $ collIf findf v ces t
collIfPrim findf v ces (APrim _ _ PrimIf [cond, t, e])
  | (Just cs) <- getConsts findf (== v) cond =
        Just $ collIf findf v (zip (map snd cs) (repeat t) ++ ces) e
collIfPrim findf v ces (APrim _ _ PrimCase (v':d:ces')) | v == v' =
        Just (reverse ces ++ makePairs ces', d)
collIfPrim _ _ ces d = Nothing


-- Given a find function (from an Id to its Expr),
-- and a function which tells whether to consider the current expression
-- (either "const True" or "== v"),
-- return "Just vcs"
--    if the expression has one or more expressions like "(v == c)" OR'd
--    together, where vcs is a mapping from v to c
--    (if the expression is a def, follow its definition)
-- return Nothing otherwise
getConsts :: (AId -> AExpr) -> (AExpr -> Bool) -> AExpr -> Maybe [(AExpr, AExpr)]
getConsts find p (APrim _ _ PrimEQ [v, c]) | p v && isInt c = Just [(v, c)]
getConsts find p (APrim _ _ PrimBOr es) = mapM (getConsts find p) es >>= return . concat
getConsts find p (ASDef _ i) = getConsts find p (find i)
getConsts find _ _ = Nothing

integerToAExprs :: Integer -> Integer -> [AExpr]
integerToAExprs n i = map (aSBool . (== 1)) (integerToBits n i)

-- Flatten a concatenation so that nested concats are merged, and
-- if "cmuxo" then split a constant into its separate bits, all to
-- be concat'd together.  Use the "get" function to follow variable
-- references.
-- XXX note that following refs can lead to inlining
-- (cmuxo is the optMuxConst flag)
aFlattenConc :: Bool -> (AId -> AExpr) -> AExpr -> [AExpr]
aFlattenConc cmuxo getf ex = flatConc ex
  where flatConc e@(ASDef _ i) =
            case getf i of
            APrim _ _ PrimConcat es -> concatMap flatConc es
            _ -> [e]
        flatConc (APrim _ _ PrimConcat es) = concatMap flatConc es
        flatConc (ASInt _ (ATBit n) (IntLit { ilValue = i })) | cmuxo = integerToAExprs n i
        flatConc e = [e]


---
isASimple :: AExpr -> Bool
isASimple (ASInt _ _ _) = True
isASimple (ASDef _ _)   = True
isASimple (ASPort _ _)  = True
isASimple (ASParam _ _) = True
isASimple (ASStr _ _ _) = True
isASimple (ASAny _ _)   = True
isASimple (APrim _ _ PrimExtract _) = True
isASimple _             = False


-- For a case on a bit-vector of size n, with "clen" number of cases,
-- if (2^n - clen) > (2^n / 3) and (n >= 3) or the default case is
-- not simple (a const or a var), then just sort the arms.
-- Otherwise, fill in the gaps with arms for the default case.
-- Also, fill in the missing arm if there's only one (then AVerilogUtil
-- will generate a full case without a default).  (This is needed because
-- the last arm of a case-statement might have been optimized away, if the
-- default was don't-care.)
-- This function assumes that the arms have been filtered for duplicate
-- indices.
-- XXX this doesn't signal back whether we have made a complete case,
-- XXX so that it can remove the default arm (or add a pragma)
complete :: AType -> AExpr -> [(AExpr,AExpr)] -> [(AExpr,AExpr)]
complete t@(ATBit nx) d cepairs =
  let
      -- the maximum number of cases
      maxlen = 2^nx
      -- the actual number of cases
      len = genericLength cepairs

      -- the cases arms sorted
      cmpIndex (x,_) (y,_) = cmpASInt x y
      sortedPairs = sortBy cmpIndex cepairs

      -- step through the sorted list of case arms.
      -- if a gap is found, fill it in with arms for the default expression.
      -- Also consider is there are redundant conditions in the arms!
      step :: Integer -> [(AExpr, AExpr)] -> [(AExpr, AExpr)]
      step n [] | n >= maxlen  = []
      step n _ | n >= maxlen = internalError ("AOpt::complete::step: " ++
                                              "arm out of range: " ++
                                              ppReadable (n, maxlen));
      step n (ce@(ASInt _ _ (IntLit { ilValue = i }), e) : ces)
          | (n == i)  = ce : step (n+1) ces
          | (n > i)   = internalError ("AOpt::complete::step: " ++
                                       "duplicate arms: " ++
                                       ppReadable (n,i) ++
                                       ppReadable cepairs)
      step n ces =
          let new_c = (ASInt defaultAId t (ilDec n)) -- XXX size the literal?
          in  (new_c, d) : step (n+1) ces

  in
     if -- there's only one arm missing
        (len == maxlen - 1) ||
        -- or there's less than a third missing,
        ( (maxlen - len <= maxlen `div` 3) &&
          -- and it's an inlineable expression
          (isASimple d) &&
          -- and the case isn't too large
          (maxlen < 8) )
     then
         -- then fill in the missing arm(s)
         step 0 sortedPairs
     else
         sortedPairs

complete _ _ _ = internalError( "AOpt::complete" )

rmDupsInCasePairs :: [(AExpr,AExpr)] ->  [(AExpr,AExpr)]
rmDupsInCasePairs prs = rmDups S.empty prs
    where
      rmDups :: S.Set Integer -> [(AExpr,AExpr)] -> [(AExpr,AExpr)]
      rmDups set [] = []
      rmDups set ( (p@(ASInt _ _ (IntLit { ilValue = n })), a) : rest )
          | n `S.member` set = rmDups set rest
          | otherwise = (p,a) : rmDups (S.insert n set) rest
      rmDups set ((p,a):rest) =
          internalError ("rmDupsInCasePairs: " ++ ppReadable p)

------------------------------------------------------------------------------------

-- these function optimize the case pair expressions for a mux
-- the following optimization occur
--  removes any pair where the condition is false
--  drops all pairs after a true const is found
--  merges identical expressions
optMuxPairs :: BFlags -> AId -> AType -> PrimOp -> [(AExpr,AExpr)] -> [(AExpr,AExpr)]
optMuxPairs bflgs aid dty op eps | not $ ao_mux bflgs = eps
optMuxPairs bflgs aid dty op eps = eps3
    where
      -- take while the pred is true, and then the first elements where pred is false
      takeWhilePlus1 :: (a -> Bool) -> [a] -> [a]
      takeWhilePlus1 predf []                 = []
      takeWhilePlus1 predf (x:xs) | predf x   = x : takeWhilePlus1 predf xs
                                  | otherwise = [x]
      -- remove any pairs where the condition is False
      eps1 = filter (not . isFalse . fst) eps
      -- drop terms after the first true term
      eps2 = takeWhilePlus1 (not . isTrue . fst) eps1
      eps3 = mergeIdenExpr op eps2

-- merge Identical Expressions
-- The sort function here can cause reordering in case expression, which can
-- later turn to if expressions, and look totally wrong when comparing to older versions.
mergeIdenExpr :: PrimOp -> [(AExpr,AExpr)] ->  [(AExpr,AExpr)]
mergeIdenExpr op eps = if ( length newpairs < length eps ) then newpairs else eps
    where
      flattenGrps :: [(AExpr,AExpr)] -> (AExpr,AExpr)
      flattenGrps [] = internalError( "AOpt::mergeIdenExpr" )
      flattenGrps [a] = a
      flattenGrps exps = (aOrs (map fst exps), snd (headOrErr "mergeIdenExpr" exps))
      --
      -- We need to have any ASAny as the last expr in group
      -- required deriving Ord to place ASAny late in the list XXX
      sortPairASAny :: [(AExpr,AExpr)] -> [(AExpr,AExpr)]
      sortPairASAny [] = []
      sortPairASAny xps =  res
          where gpd :: [[(AExpr,AExpr)]]
                gpd = groupBy (testf) (sortBy cmpSnd xps)
                res = case gpd of
                        [ x ] -> x
                        [ x,y ] -> x ++ y
                        x -> internalError( "Aopt::mergeIdenExpr: " ++ ppReadable eps ++ ppReadable x)
                --
                testf :: (AExpr,AExpr) -> (AExpr,AExpr) -> Bool
                testf (_,x1) (_,x2) = isASAny x1 == isASAny x2
      --
      sortfn = if (op == PrimMux) then (sortPairASAny . sortBy cmpSnd) else id
      meps = groupBy eqSnd (sortfn eps)
      newpairs = map flattenGrps meps


------------------------------------------------------------------------------------
-- muxOpt
-------------

-- a pass of all PrimPriMux and PriMux to remove constants and
-- to turn small ones back to if
muxOptConst :: BFlags -> AId -> AType -> PrimOp -> [AExpr] -> O AExpr
muxOptConst bflgs aid dty op exs | not $ ao_mux bflgs = return (APrim aid dty op exs)
muxOptConst bflgs aid dty op exs = do
    -- trivial mux opt
    -- optimize the pairs
    let exs1 = optMuxPairs bflgs aid dty op (makePairs exs)
        bflgs' = optFlagsOff bflgs
    case exs1 of
      []                               -> internalError "muxOptConst"
      [(c,e)]                           -> return e
      {- The test for is True must be use formal technology to prove it
      [(c,e)] | isTrue c               -> return e
              | otherwise              -> internalError( "AOpt::muxOpt " ++ ppReadable exs  ++ ppReadable (c,e) )
              -}
      -- 2 input mux, with ASAny as second arm
      [(_,e),(_,(ASAny {}))]           -> return e
      -- 3 input with ASAny convert to if the else
      [(c,e1),(_,e2),(_,(ASAny {}))]   -> aPrim bflgs' aid dty PrimIf [c,e1,e2]
      -- A 2 input mux is turned into a if regardless of flags.
      [(c,e1),(_,e2)]                  -> aPrim bflgs' aid dty  PrimIf [c,e1,e2]
      -- otherwise just build the mux back again
      es                               ->  return (APrim aid dty op (flattenPairs es ))


-------------------------------------
-- Previous mux opt -- turned off now.

isAnyExprAString :: [AExpr] -> Bool
isAnyExprAString exprs = any isAExprStr exprs
    where isAExprStr :: AExpr -> Bool
          isAExprStr (ASStr {} ) = True
          isAExprStr _           = False

-- function which optimizes mux pairs
muxOpt :: BFlags -> AId -> AType -> PrimOp -> [AExpr] -> O AExpr
muxOpt bflgs aid dty op esx | not $ ao_muxExpand bflgs = do
    -- trivial mux opt
  return $
    case esx of
            []          -> internalError "muxOpt"
            [_,e]       -> e
            [c,e1,_,e2] -> APrim aid dty PrimIf [c,e1,e2]
            es          -> APrim aid dty op es

-- Do not do Mux optimization if any expr is a string
muxOpt bflgs aid dty op esIn | ao_muxExpand bflgs && isAnyExprAString esIn =
  muxOpt (optFlagsOff bflgs)  aid dty op esIn

-- (if optMux flag is True)
-- this is not used by default since it leads to bad QOR.
muxOpt bflgs aidx dty op esIn | ao_muxExpand bflgs  = do
    when debug2 $ traceM ("--------------------------------------------------------------------------------------" )
    when debug2 $ traceM ("Type: " ++ ppReadable dty)
    when debug2 $ traceM ("muxOpt " ++ ppReadable (APrim aidx dty op esIn))
    getf <- findDef
    let (psIn, asIn) = unzip (makePairs esIn)
        cmuxo = ao_muxconst bflgs
    --
    -- for each expr returned by the branch of the mux (for each "a" in "as"),
    -- return back a list of exprs which concatenated together form "a"
    -- (if "a" is not a concatenation, then you get back a single elem list),
    -- and all subconcatenations are flattened into this one list
    -- (note that variable references are inlined if they reveal a sub-concat).
    -- finally, the elements of the list are turned into simple exprs
    -- (any which are not simple are assigned to a new signal name and
    -- replaced with a reference to that signal).
    --
    ess <- mapM (mapM mkDefS) (map (aFlattenConc cmuxo getf) asIn)
    let
        -- Concatenations are broken apart to mux the separate pieces?
        -- For Strings, the aSize function returns string size *8 which is bad in this case
        -- szs represents all the break points for the various c exprs which are concats.
        -- for each "es" in "ess" (corresponding to the pieces concatenated
        -- to form the value for one branch),
        --   * get the size of each piece
        --   * produce the list of indices for the start of each piece:
        --     given the lengths [1,2,3] produces [6,5,3,0]
        -- from these lengths, one ordered list of all indices is made
        -- (indicating each location where a concat on some branch starts)
        --
        szs = (remOrdDup . sort . concatMap (scanr (+) 0 . map aSize)) ess
        -- XXX need to CSE expressions that are split
    let
        -- lists of the concatenated pieces for each branch of the mux
        ess' = map (reverse . splitEs 0 szs . reverse) ess
         -- to turn mux of concats into a concat of muxes, transpose the
        -- list into lists for each mux containing the same segment from
        -- each value
        tess = transpose ess'
    let
        mxs = map (mux psIn) tess
        mux :: [AExpr] -> [AExpr] -> AExpr
        mux pxs exs@(ex:_) = mux' [] pxs exs
            where mux' :: [(AExpr,AExpr)] -> [AExpr]  -> [AExpr] -> AExpr
                  mux' xs [] []                     = aMakeMux aidx t op (reverse xs)
                  mux' xs (_:ps) ((ASAny _ _) : es) = mux' xs ps es
                  mux' xs (p:ps) (e:es)             = mux' ((p,e):xs) ps es
                  mux' xs ps es                     = internalError( "AOpt::mux' " ++ ppReadable (xs,ps,es) )
                  -- list ps and es must be same size
                  t = aType ex
        mux _ _  = internalError( "AOpt::mux" )
    let
        jms = joinMuxes mxs
        joinMuxes :: [AExpr] -> [AExpr]
        joinMuxes (m:m':ms) =
            case join2 m m' of
            Nothing  -> m : joinMuxes (m':ms)
            Just m'' -> joinMuxes (m'':ms)
        joinMuxes ms = ms
        join2 (APrim aid ty p pes) (APrim _ _ p' pes') | length pes == length pes'
                                && p == p' && (p == PrimMux || p == PrimPriMux) = do
            pes'' <- joinpes pes pes'
            return (APrim aid (aType (pes''!!1)) p pes'')
{-
-- XXX why is this commented out?  it looks like a good optimization!
        join2 (APrim _ ty PrimIf [c,t,e]) (APrim _ _ PrimIf [c',t',e']) | c == c' = do
            let t'' = aConcat [t, t']
                e'' = aConcat [e, e']
            return (APrim _ (aType t'') PrimIf [c,t'',e''])
-}
        join2 _ _ = Nothing
        joinpes (p:e:pes) (p':e':pes') =
            if p == p' then do
                pes'' <- joinpes pes pes'
                return (p:(aConcat [e, e']):pes'')
            else
                Nothing
        joinpes [] [] = return []
        joinpes xs ys = internalError ("joinpes " ++ ppReadable (xs, ys))
--        trace (ppReadable d ++ ppReadable ess
--                ++ ppReadable (concatMap concat dsss)
--                ++ ppReadable szs ++ ppReadable ess'
--                ++ ppReadable tess ++ ppReadable ps ++ ppReadable ms ++ ppReadable d')
        aOptMuxSel :: AExpr -> AExpr
        aOptMuxSel (APrim aid t p pes) | p == PrimMux || p == PrimPriMux =
                APrim aid t p (flattenPairs (mapFst aBoolSimp (makePairs pes)))
        aOptMuxSel _ = internalError "aOptMuxSel"
        result = aConcat (map (aTransAndOrMux . aTransMux . aOptMuxSel) jms)
    --
    when debug2 $ traceM ("muxOpt result:" ++ ppReadable result)
    return result

muxOpt _ aid _ _ _ = internalError ("AOpt::muxOpt unexpected" ++ ppReadable aid)

-- Utility function used in mux optimzation
-- Given:
--   offs = the offset into the current "e"
--          (how much of the current "e" has already been chewed off)
--   l = the low index point for the next segment to consider
--   h = the high index point
--   (e:es) = a list of expressions which concatenated together
--            form one expression (returned by one branch of the mux)
--            (the exprs are in reverse order, so "e" is the right
--            most expr, with the lowest index)
--            "e" is the piece to start chewing on
splitEs :: Integer -> [Integer] -> [AExpr] -> [AExpr]
splitEs offs (l:ss@(h:_)) (e:es) =
            let
                -- the size of the next piece
                s = aSize e
                -- the distance from the current index to the next index
                d = h - l
            in
                -- if the amount chewed from "e" so far plus the distance
                -- to go is exactly the size of the "e" ...
                if offs + d == s then
                    -- then if the amount chewed is 0, just output "e".
                    -- otherwise, select the portion remaining from "e".
                    -- in either case, continue chewing on "es" starting
                    -- with the next index ("ss") and reset offset back to 0
                    if offs == 0 then
                        e : splitEs 0 ss es
                    else
                        aSelect e offs d : splitEs 0 ss es
                else
                    -- otherwise, it must be less than "s", because we
                    -- know that the sizes list contains an index for
                    -- end of every "e". so...
                    -- select the next distance from "e" and
                    -- continue with the next index, incrementing the
                    -- offset by "d", and still chewing on "e"
                    aSelect e offs d : splitEs (offs+d) ss (e : es)
        -- if "es" is empty, or if the index list is 1 elem or less,
        -- return nothing
splitEs _ _ _ = []

-- Given a list of expressions to be concatenated (args to PrimConcat),
-- expand out any which are themselves calls to PrimConcat, to get one
-- flattened list of all expressions to be concatenated (in order).
-- If any two are bit extractions with consecutive ranges, them join them
-- into one expression extracting over the entire range.  (By calling
-- aExtract, that should check whether the extract is over the entire range
-- and will just use the expr in its entirety, with no extraction.)
-- If any two neighboring exprs in the concat are constants, then join
-- them into one constant.
aConcat :: [AExpr] -> AExpr
aConcat exs =
    let joinPairs :: [AExpr] -> [AExpr]
        joinPairs ((APrim aid _ PrimExtract
                        [e,  ASInt _ _ (IntLit _ _ hi), ASInt _ _ (IntLit _ _ lo) ]) :
                   (APrim aid' _ PrimExtract
                        [e', ASInt _ _ (IntLit _ _ hi'), ASInt _ _ (IntLit _ _ lo')]) :
                as) | e == e' && lo == hi' + 1 =
                        joinPairs (aExtract e hi lo' : as)
        joinPairs ((ASInt aid (ATBit s) (IntLit _ b i)) : (ASInt aid' (ATBit s') (IntLit _ _ i')) : as) =
                        -- XXX the literal has no width
                        joinPairs ((ASInt aid (ATBit (s+s')) (IntLit Nothing b (i*2^s' + i'))) : as)
        joinPairs (a:as) = a : joinPairs as
        joinPairs [] = []
        flat (APrim _ _ PrimConcat es) = concatMap flat es
        flat e = [e]
    in  case joinPairs (concatMap flat exs) of
        [e] -> e
        es -> APrim defaultAId (ATBit (sum (map aSize es))) PrimConcat es

aSelect :: AExpr -> Integer -> Integer -> AExpr
aSelect (ASAny _ _) _ d = ASAny (ATBit d) Nothing
aSelect (ASInt aid _ (IntLit w b i)) offs d =
        ASInt aid (ATBit d) (IntLit Nothing b (integerSelect d offs i))
aSelect (APrim aid _ PrimExtract [e, (ASInt _ _ _), ASInt _ _ (IntLit _ _ lo)]) offs d =
        APrim aid (ATBit d) PrimExtract [e, aNat (offs+d-1+lo), aNat (offs+lo)]
aSelect e0@(APrim aid _ PrimConcat exs) offs dx =
    let (es', offs') = chopL (reverse exs) offs
                        where chopL (e:es) o | s <= o = chopL es (o-s) where s = aSize e
                              chopL es o = (es, o)
        es'' = chopH es' (dx+offs')
                        where chopH (e:es) d | d > 0 = e : chopH es (d - aSize e)
                              chopH _ _ = []
    in  case reverse es'' of
        [] -> internalError ("aSelect PrimConcat " ++ ppReadable (e0, offs, dx))
        [e] -> aSelect e offs' dx
        ses ->        let ce = APrim aid (ATBit (sum (map aSize ses))) PrimConcat ses
                in APrim aid (ATBit dx) PrimExtract [ce, aNat (offs'+dx-1), aNat offs']

aSelect e offs d = APrim defaultAId (ATBit d) PrimExtract [e, aNat (offs+d-1), aNat offs]

aExtract :: AExpr -> Integer -> Integer -> AExpr
aExtract e hi 0 | hi+1 == aSize e = e
aExtract e hi lo =
        APrim
            defaultAId
            (ATBit (hi-lo+1))
            PrimExtract [e, aNat hi, aNat lo]

------------

aMakeMux :: AId -> AType -> PrimOp -> [(AExpr, AExpr)] -> AExpr
aMakeMux aid t op pexs =
    let pexs' = joinEq (if op == PrimMux then partition else span) pexs
        joinEq f [] = []
        joinEq f ((p,e):pes) =
            let (xs, pes') = f (aEqual e . snd) pes
            in  (aOrs (p : map fst xs), e) : joinEq f pes'
        aEqual :: AExpr -> AExpr -> Bool
        aEqual (ASInt _ _ (IntLit _ _ i)) (ASInt _ _ (IntLit _ _ i')) = i == i'
        aEqual e e' = e == e'
    in  APrim aid t op (flattenPairs pexs')

aIf :: AType -> AExpr -> AExpr -> AExpr -> AExpr
aIf ty c (ASInt _ _ (IntLit _ _ 1)) (ASInt _ _ (IntLit _ _ 0)) = aZeroExt ty c
aIf ty c (ASInt _ _ (IntLit _ _ 0)) (ASInt _ _ (IntLit _ _ 1)) =
        aZeroExt ty (aBoolSimp (APrim dummy_id aTBool PrimBNot [c]))
aIf ty@(ATBit 1) c t e = aBoolSimp (APrim dummy_id ty PrimIf [c, t, e])
aIf ty c t e = APrim dummy_id ty PrimIf [c, t, e]

-- Zero extend the aexpr to the type specified.   Assumes a AExpr is 1 bit !!!
aZeroExt :: AType -> AExpr -> AExpr
aZeroExt (ATBit 1) e = e
aZeroExt ty@(ATBit sz) e = APrim dummy_id ty PrimConcat
                [ASInt defaultAId
                        (ATBit (sz-1)) (ilDec 0), e]
aZeroExt _ _ = internalError( "AOpt::aZeroExt" )

-- This is only called by muxOpt, which only optimizes PrimMux and PrimPriMux
aTransMux :: AExpr -> AExpr
aTransMux (APrim _ t _ []) = ASAny t Nothing -- ok for both types
aTransMux (APrim _ _ _ [_, e]) = e     -- ok for both types
aTransMux (APrim aid t PrimMux [p1, e1, p2, e2]) =
        if isASimple p2 && not (isASimple p1)
                then aIf t p2 e2 e1
                else aIf t p1 e1 e2
aTransMux (APrim aid t PrimPriMux [p1, e1, p2, e2]) = aIf t p1 e1 e2
aTransMux e@(APrim {}) = e
aTransMux _ = internalError( "AOpt::aTransMux" )

aTransAndOrMux :: AExpr -> AExpr
aTransAndOrMux (APrim aid t PrimMux pes) =
    -- all inputs that are 0 can be removed from an AND/OR mux
    let pes' = filter (isNonZero . snd) (makePairs pes)
        isNonZero (ASInt _ _ (IntLit _ _ 0)) = False
        isNonZero _ = True
    in  if t == aTBool then
            -- turn a boolean mux into the corresponding expression.
            aBoolSimp (APrim aid t PrimBOr [ APrim aid t PrimBAnd [p, e] | (p, e) <- pes' ])
        else
            APrim aid t PrimMux (flattenPairs pes')
aTransAndOrMux e = e

------------

-- simplify boolean expressions
-- This has the desired behavior of flattening out ors of ors and ands of ands
-- see testcase for bug 292
aBoolSimp :: AExpr -> AExpr
aBoolSimp e =
    let r = (fromBE . nSimplify . toBE {- . aOrAnd-}) (optXor e)
    in  --traces (ppReadable (e, r))
        r

{-
-- a quick and dirty optimization of or-and expressions that are generated for the scheduler
aOrAnd :: AExpr -> AExpr
aOrAnd e@(APrim _ t PrimOr es@(_:_)) =
        let es' = map (S.fromList . getOp PrimBAnd) es
            common = foldr1 S.intersect es'
            es'' = map (mkAnd . S.toList . (`S.minus` common)) es'
            mkAnd :: [AExpr] -> AExpr
            mkAnd [] = aBool True
            mkAnd [e] = e
            mkAnd es = APrim _ aTBool PrimBAnd es
        in  if S.null common then
                e
            else
                APrim _ aTBool PrimBAnd (APrim _ aTBool PrimBOr es'') : S.toList common
aOrAnd e = e

aOrAndS e = e
-}

optXor :: AExpr -> AExpr
optXor (APrim _ t PrimXor [ASInt aid _ (IntLit _ _ x), ASInt _ _ (IntLit _ _ y)]) =
        ASInt aid t (ilSizedBin 1 ((x+y)`mod`2))
optXor (APrim _ t PrimXor [ASInt _ _ (IntLit _ _ 0), y]) = y
optXor (APrim aid t PrimXor [ASInt _ _ (IntLit _ _ 1), y]) = aNotLabel aid y
optXor (APrim _ t PrimXor [x, ASInt _ _ (IntLit _ _ 0)]) = x
optXor (APrim aid t PrimXor [x, ASInt _ _ (IntLit _ _ 1)]) = aNotLabel aid x
optXor (APrim _ t PrimXor [x, x']) | x == x' = aBool False
optXor (APrim _ t PrimXor [x, APrim _ _ PrimBNot [x']]) | x == x' = aBool True
optXor (APrim _ t PrimXor [APrim _ _ PrimBNot [x], x']) | x == x' = aBool True
optXor e = e

toBE :: AExpr -> BoolExp AExpr
toBE (APrim _ _ PrimBAnd es) = foldr1 And (map toBE es)
toBE (APrim _ _ PrimBOr  es) = foldr1 Or  (map toBE es)
toBE (APrim _ _ PrimBNot [e]) = Not (toBE e)
toBE (APrim _ _ PrimIf [c,t,e]) = If (toBE c) (toBE t) (toBE e)
toBE (ASInt _ _ (IntLit _ _ b)) = if b == 1 then TT else FF
toBE e = Var e

fromBE :: BoolExp AExpr -> AExpr
fromBE (And b1 b2) = APrim defaultAId aTBool PrimBAnd
                           (getOp PrimBAnd (fromBE b1) ++
                            getOp PrimBAnd (fromBE b2))
fromBE (Or  b1 b2) = APrim defaultAId aTBool PrimBOr
                           (getOp PrimBOr  (fromBE b1) ++
                            getOp PrimBOr  (fromBE b2))
fromBE (Not b) = APrim defaultAId aTBool PrimBNot [fromBE b]
fromBE (If c t e) = APrim defaultAId aTBool PrimIf [fromBE c, fromBE t, fromBE e]
fromBE (Var e) = e
fromBE TT = aBool True
fromBE FF = aBool False

getOp :: PrimOp -> AExpr -> [AExpr]
getOp p (APrim _ _ p' es) | p == p' = es
getOp _ e = [e]

------------
-- optAndOrDef
-- this optimization use the SAT solver to reconstruct And/Or
-- expressions,  checking if the term in the expression is redundant
-- with the existing expression.   redundant expression are of course
-- dropped.
-- The solver is in the IO monad and we use StateT to hold its state.
-- The monad holds the state during analysis of one def, but we do not
-- retain any useful state between defs.
-- Note also that this optimization does not descend into defs.
-- XXX Both of these decisions were made because of the performance of
-- XXX CUDD as the solver.  With Yices, we may be able to maintain state
-- XXX across defs and to follow non-inlined defs.

type SIO a = StateT SATState IO a

-- This can pass over each ADef and optimize the expression looking
-- for redundant and or terms
optAndOrDefs :: String -> ErrorHandle -> Flags -> [ADef] -> IO [ADef]
optAndOrDefs str errh flags defs | not $ optAndOr flags = return defs
optAndOrDefs str errh flags defs = do
  -- soft fail, no defs
  s <- initSATState str errh flags False [] []
  evalStateT (mapM optAndOrDef defs) s

optAndOrDef :: ADef -> SIO ADef
optAndOrDef adef@(ADef i t e p) = do
  when debug2 $ traceM( "optAndOrDefs: " ++ ppReadable adef)
  e1 <- optAndOrExpr e
  when debug2 $ traceM( "optAndOrDefs: result " ++ ppReadable e1)
  return (ADef i t e1 p)

-- The main worker function
optAndOrExpr :: AExpr -> SIO AExpr
-- process And Expressions
-- Note that the use of reverse here is a heuristic. based on how we build these expressions
-- We may want to do a pass each way?
optAndOrExpr (APrim i t@(ATBit 1) op es)
    | (op == PrimBAnd) || (op == PrimAnd) = do
  es1 <- mapM optAndOrExpr es
  let (e1, er1) = unconsOrErr "AOpt.optAndOrExpr And" (reverse es1)
  es2 <- foldM testBuildAnd [e1] er1
  checkIfConst  $ case es2 of
                    [e] -> e
                    es3 -> (APrim i t op (es3))
--
-- Optimize Or expressions
optAndOrExpr (APrim i t@(ATBit 1) op es)
    | (op == PrimBOr) || (op == PrimOr) = do
  es1 <- mapM optAndOrExpr es
  let (e1,er1) = unconsOrErr "AOpt.optAndOrExpr Or" (reverse es1)
  es2 <- foldM testBuildOr [e1] er1
  checkIfConst $ case es2 of
                   [e] -> e
                   es3 -> (APrim i t op (es3))

--
-- traverse down other prim expressions
optAndOrExpr (APrim i t op es) = do
  es1 <- mapM optAndOrExpr es
  return (APrim i t op es1)
--
-- ignore other expressions
optAndOrExpr e = return e


testBuildAnd :: [AExpr] -> AExpr -> SIO  [AExpr]
testBuildAnd aas b = do
  s <- get
  let aaE = case aas of
              [a] -> a
              _   -> (APrim defaultAId aTBool PrimBAnd aas)
  ((aImpliesB,bImpliesA), s1) <- liftIO $ checkBiImplication s aaE b
  put s1
  -- liftIO $ putStrLn ("testBuildAnd: " ++ show (length aas))
  return $ case (aImpliesB,bImpliesA) of
             (True, _ ) -> aas
             (_, True ) -> [b]
             (_,_     ) -> b:aas

testBuildOr :: [AExpr] -> AExpr -> SIO  [AExpr]
testBuildOr aas b = do
  s <- get
  let aaE = case aas of
              [a] -> a
              _   -> (APrim defaultAId aTBool PrimBOr aas)
  ((aImpliesB,bImpliesA), s1) <- liftIO $ checkBiImplication s aaE b
  put s1
  return $ case (aImpliesB,bImpliesA) of
             (True, _ ) -> [b]
             (_, True ) -> aas
             (_,_     ) -> b:aas


checkIfConst :: AExpr -> SIO AExpr
checkIfConst expr =
    do
       s <- get
       (mconst, s1) <- liftIO $ isConstExpr s expr
       put s1
       case mconst of
         Just True  -> return aTrue
         Just False -> return aFalse
         Nothing    -> return expr


-- -------------------------------------------------------------
-- optExpr reusing aPrim to accomplish some simple optimization
-- used before dumpSERI / dump lambda calculus phase
-- inline some expressions  (PrimBNot,  extract of constants)
-- join multiple concats (uses aPrim)
-- remove unused defs
aOptAPackageLite :: ErrorHandle -> Flags -> APackage -> APackage
aOptAPackageLite errh flags apkg =
    --trace ("Defs -- pre: " ++ ppReadable  apkg) $
    --trace ("Defs -- 1: " ++ ppReadable (apkg_local_defs apkg1)) $
    --trace ("Defs -- 2: " ++ ppReadable (apkg_local_defs apkg2)) $
    apkgN
  where
      -- Expand to inline some defs
      apkg1 = expandAPackage errh apkg
      -- Optimize expressions
      (ds1) = aOptPackage1 apkg1
      apkg2 = apkg1 { apkg_local_defs = ds1 }
      -- remove unused defs
      apkg3 = apkg2  -- XXX ?
      -- final pass (to merge AND/OR operators)
      -- XXX this doesn't do much, though, because we haven't inlined the ops
      -- XXX (see AExpand::isSeriInline)
      apkgN = aOptFinalPass flags apkg3

aOptPackage1 :: APackage -> ([ADef])
aOptPackage1 apkg =
  let optF = do
        ds <- mapM aOptDefLite (apkg_local_defs apkg)
        return ds
  in evalState optF initOState


aOptDefLite :: ADef -> O ADef
aOptDefLite adef = do
  e' <- aOptExprLite (adef_expr adef)
  return adef { adef_expr = e' }

aOptExprLite ::AExpr -> O AExpr
aOptExprLite (APrim aid t p es) = aPrim optExprBFlag aid t p es
aOptExprLite e = return e
