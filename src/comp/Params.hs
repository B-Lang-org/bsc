module Params(
	      id_Params,
	      -- a specific stage on ISyntax for handling params
	      iParams,
	      -- functions for checking if a param's expr is legal
	      -- (is a constant expression, as defined by Verilog)
	      isConstIExpr, isConstAExpr
	     ) where

import qualified Data.Map as M
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle, bsError)
import PPrint
import Id
import Position
import ISyntax
import ASyntax
import VModInfo
import Prim


id_Params = " $Id: Params.hs 7659 2005-10-26 21:28:16Z quark $"

-- ==========

-- XXX This could become part of IExpand.handlePrim on ICVerilog,
-- XXX instead of being a separate pass.
iParams :: ErrorHandle -> IModule a -> IO (IModule a)
iParams errh imod =
    let
	ds = imod_local_defs imod
	ss = imod_state_insts imod

	{-
	-- XXX not needed because we don't need to know the Ids,
	-- XXX because the references are marked as ICModParam
	size_ps = imod_type_args imod
	inputs = imod_wire_args imod
	wi = imod_external_wires imod
	varginfo = wArgs wi

	-- identify which inputs are parameters
	param_inputs = [ i | (i, Param {}) <- zip inputs varginfo ]

	param_ids = map fst size_ps ++
	            map fst param_inputs
	-}

	-- create a map of ids and the exprs they inline to
	-- (with each expr already itself inlined completely)
	-- (assuming that "ds" is tsorted)
        --dmap :: M.Map Id (IExpr a)
	dmap = M.fromList [ (i, iSubst dmap e) | IDef i _ e _ <- ds ]

	ss' = map (inlineParams dmap) ss
	imod' = imod { imod_state_insts = ss' }

	emsgs = concatMap checkParams ss'
    in
	if (null emsgs)
	then return imod'
	else bsError errh emsgs


inlineParams :: M.Map Id (IExpr a) -> (Id, IStateVar a) -> (Id, IStateVar a)
inlineParams dmap (inst, svar) =
    let
	-- get the relevant fields from the IStateVar
	varginfo = vArgs (isv_vmi svar)
	es = isv_iargs svar

	-- for each parameter instantiation argument,
	-- inline variables references in its instantiation expression
	inlineParam (Param {}, expr) = iSubst dmap expr
	inlineParam (_, expr) = expr

	-- create the new IStateVar to return
	es' = map inlineParam (zip varginfo es)
	svar' = svar { isv_iargs = es' }
    in
	(inst, svar')


checkParams :: (Id, IStateVar a) -> [EMsg]
checkParams (inst, svar) =
    let
	-- get the relevant fields from the IStateVar
	varginfo = vArgs (isv_vmi svar)
	arg_es = isv_iargs svar

	-- position for reporting errors
	pos = getPosition inst

	-- users only know the instantiation arguments by position,
	-- so zip with a number indicating the position
	triples = zip3 [1..] varginfo arg_es

	-- check a single param
	checkParam :: (Integer, VArgInfo, IExpr a) -> [EMsg]
	checkParam (n, varginfo@(Param {}), expr) =
	    if (not (isConstIExpr expr))
	    then let port_name = getIdString (getVArgInfoName varginfo)
		     inst_name = getIdString inst
		 in  [(pos, EModParameterDynamic inst_name port_name)]
	    else []
	checkParam _ = []
    in
	concatMap checkParam triples


-- XXX copied from IInline; consider putting it in one place?
iSubst :: M.Map Id (IExpr a) -> IExpr a -> IExpr a
iSubst m e = sub e
  where sub (IAps f ts es) = IAps (sub f) ts (map sub es)
	sub d@(ICon i _) =
	    case M.lookup i m of
	    Nothing -> d
	    Just e -> e
	sub ee = internalError ("iSubst: " ++ ppReadable ee)


-- ==========

isConstIExpr :: IExpr a -> Bool
isConstIExpr (ICon _ (ICInt {} )) = True       -- constant number
isConstIExpr (ICon _ (ICReal {} )) = True      -- constant number
isConstIExpr (ICon _ (ICString {} )) = True    -- constant string
isConstIExpr (ICon _ (ICModParam {} )) = True  -- parameter reference
isConstIExpr (ICon _ (ICUndet {} )) =
    -- Undetermined values will become constant values
    True
isConstIExpr (ICon _ (ICDef {})) =
    -- Local def references should have been inlined away
    internalError "Params.isConstIExpr: inlining not complete"
isConstIExpr (ICon _ (ICPrim {})) =
    -- primitive operators should be applied,
    -- there is no 0-arity primitive that we allow
    False
isConstIExpr (ICon _ (ICCon {} )) =
    -- Constructors should be turned into bits by now
    -- XXX check this!
    False
isConstIExpr (IAps f _ es) =
    -- application of acceptible operators on constant args is constant
    (isConstIExprFunc f && all isConstIExpr es)
isConstIExpr _ = False


isConstIExprFunc :: IExpr a -> Bool
-- XXX this should check for only prims which can be turned into
-- XXX acceptible Verilog primitives, and return False for others
isConstIExprFunc (ICon _ (ICPrim {})) = True
-- tuples, selector functions, constructor selectors etc, should all
-- have been evaluated away, leaving only bits
isConstIExprFunc _ = False


-- ==========

-- Check that expressions for submodule instantiation parameters are
-- "constant expressions": literals, top-level parameters, or certain
-- primitive operations on those.

-- The first argument is a list of ASPort names which can be assumed
-- to have constant values
isConstAExpr :: [AId] -> AExpr -> Bool
isConstAExpr _ (ASInt {}) = True     -- constant number
isConstAExpr _ (ASReal {}) = True    -- constant real number
isConstAExpr _ (ASStr {}) = True     -- constant string
isConstAExpr _ (ASParam {}) = True   -- parameter reference
isConstAExpr ps (ASPort _ port_id) = 
    -- ports are dynamic unless we're told to assume them constant
    (port_id `elem` ps)
isConstAExpr _ (ASAny {}) =
    -- Undetermined values will become constant values
    True
isConstAExpr _ e@(ASDef {}) =
    -- Local def references should have been inlined away
    internalError ("Params.isConstAExpr: inlining not complete: " ++
		   ppReadable e)
    -- XXX could have said "False" here, so that it's available
    -- XXX for other uses?
isConstAExpr ps (APrim { aprim_prim = op, ae_args = es }) =
    (isConstOp op && all (isConstAExpr ps) es)
isConstAExpr _ _ = False


-- ==========

-- XXX Should this go into Prims.hs?

-- Check whether a primitive is an acceptible operator for
-- a constant ASyntax expression.
-- (This check should not be specific to any backend.)

isConstOp :: PrimOp -> Bool
isConstOp PrimAdd  = True  -- VAdd
isConstOp PrimSub  = True  -- VSub
isConstOp PrimAnd  = True  -- VAnd
isConstOp PrimOr   = True  -- VOr
isConstOp PrimXor  = True  -- VXor
isConstOp PrimMul  = True  -- VMul

isConstOp PrimQuot = True -- VQuot
isConstOp PrimRem  = True -- VRem

isConstOp PrimSL   = True  -- VShL
isConstOp PrimSRL  = True  -- VShR
isConstOp PrimSRA  = True  -- VeriQuirks removes it?

isConstOp PrimInv  = True  -- VInv
isConstOp PrimNeg  = True  -- VNeg

isConstOp PrimEQ   = True  -- VEQ
isConstOp PrimEQ3  = True  -- VEQ3
isConstOp PrimULE  = True  -- VULE
isConstOp PrimULT  = True  -- VULT

isConstOp PrimSLE  = True  -- converted to VULT
isConstOp PrimSLT  = True  -- converted to VULE

-- These would be replaced with Concat or Extract?
isConstOp PrimSignExt = True
isConstOp PrimZeroExt = True
isConstOp PrimTrunc   = True

isConstOp PrimExtract = True
isConstOp PrimConcat  = True
-- This would also be replaced?
isConstOp PrimSplit   = True  -- not handled in AVerilogUtil

isConstOp PrimBNot      = True  -- VNot
isConstOp PrimBAnd      = True  -- VLAnd
isConstOp PrimBOr       = True  -- VLOr

-- Case statements will need to be inlined as if-expressions in
-- the Verilog backend, but we consider them constant expressions
-- if the arguments are constant
isConstOp PrimIf     = True  --  becomes VEIf ( b?x:y )
isConstOp PrimCase   = True

-- These appear as a pair and are equivalent to PrimCase/PrimIf
isConstOp PrimArrayDynSelect = True
isConstOp PrimBuildArray = True

-- XXX No reason not to allow these, but they won't occur in parameter exprs
isConstOp PrimMux    = False
isConstOp PrimPriMux = False

-- This should be transformed away too, right?
isConstOp PrimSelect = True  -- not handled in AVerilog

-- improved string parameter support
isConstOp PrimStringConcat = True

isConstOp _ = False


-- ==========

