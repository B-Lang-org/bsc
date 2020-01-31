module InlineReg (
		  vInlineReg,
		  RegInstInfo
		  ) where

import Data.List(partition)
import qualified Data.Map as M
import IntLit
import IntegerUtil(aaaa)
import Util(itos)
import PPrint
import Error
import Flags(Flags)
import Id
import ASyntax
import VModInfo
import Verilog
import AVerilogUtil
import BackendNamingConventions

-- ==============================
-- Inline registers

-- returns:
--  * the always blocks for handling the inlined registers, and
--  * info on the signals for each register (used by AVerilog):
--      * the name of the instance
--      * the list of inputs and their sizes
--      * the output, to be declared "Reg" and its size
vInlineReg :: ErrorHandle -> Flags -> [AVInst] -> ([VMItem], [RegInstInfo])
vInlineReg errh flags avis =
    let
        vco = flagsToVco flags
	-- separate the RegAs from the RegN and RegUN
	(regas, regns_and_reguns) = partition isRegA avis

	-- make a map from clock to the RegNs and RegUNs in that clock
	ns_and_uns_by_clock = M.toList (partitionByClock errh regns_and_reguns)

	-- translate the partitioned RegN/RegUNs into always blocks
	ns_and_uns_items = map (vInlineN errh vco) ns_and_uns_by_clock

	-- make a map from clock and reset to the RegAs for that pair
	as_by_clock_and_reset = M.toList (partitionByClockAndReset errh regas)

	-- translate the partitioned RegAs into always blocks
	as_items = map (vInlineA vco) as_by_clock_and_reset

	-- All the registers should all be set in an initial block --
	-- there is no guarantee that they will be reset properly
	initial = mkInitialAssignments flags avis

	-- the list of items to return
	items =  ns_and_uns_items ++ as_items ++ initial 

	-- the register I/O info for AVerilog grouping
	reg_infos = map (mkRegInstInfo errh flags) avis
    in
	(items, reg_infos)


-- ==============================

-- The name of the instance,
-- its clk and reset port expressions,
-- its inputs and their types, and
-- the output signal (to be declared "reg") and its type.
type RegInstInfo = (VId, String, [VExpr], [(VId, Maybe VRange)], (VId, Maybe VRange))

-- XXX We can either return enough info to AVerilog for it to create
-- XXX the instantiation group for the inlined register (declare the
-- XXX IO signals and the reg), or we can just do it ourselves here.
-- XXX We do the former:
mkRegInstInfo :: ErrorHandle -> Flags -> AVInst -> RegInstInfo
mkRegInstInfo errh flags avi =
    let vco = flagsToVco flags
        reg_id = vId (mkQOUT avi)
	din_id = vId (mkDIN avi)
	en_id = vId (mkEN avi)
	reg_size = case (getRegWidth avi) of
		       (ASInt _ _ (IntLit _ _ n)) -> vSize (ATBit n)
		       -- the parameter expression should be constant
		       e -> internalError ("mkRegInstInfo: " ++ ppReadable e)
	en_size = Nothing  -- no range means one bit
	-- find the special inputs (note that RegUN doesn't have a RST)
	clk_expr = vExpr vco (getRegClock errh avi)
	rstn_expr = vExpr vco (getRegReset errh avi)
	non_method_ports = if (isRegUN avi)
			   then [clk_expr]
			   else [clk_expr, rstn_expr]
	inst_id = avi_vname avi
    in
        ((VId (getIdString inst_id) inst_id Nothing),
         (getVNameString (vName (avi_vmi avi))),  -- name of the def (RegN, RegUN etc.)
	 non_method_ports,
	 [(din_id, reg_size), (en_id, en_size)],
	 (reg_id, reg_size))

-- ==============================

-- Generate an always block for RegN and RegUN on the same clock
vInlineN :: ErrorHandle -> VConvtOpts -> (AExpr, [AVInst]) -> VMItem
vInlineN errh vco (clk, avis) =
    let
	-- partition the avis into those with resets and those without
	(regns, reguns) = partition isRegN avis

	-- partition the RegNs by reset
	regns_by_reset = partitionByReset errh regns

	-- translate into statements inside the always block
	body_items =
	    -- put a comment here "initialized registers"
	    map (translateRegN vco) (M.toList regns_by_reset) ++
	    -- put a comment here "uninitialized registers"
	    map (translateRegUN vco) reguns

	-- event for the surrounding always block
	ev = VEEposedge (vExpr vco clk)

	-- use VSeq (not vSeq) so that the always block always has
	-- begin/end, even when there is only one item inside it
	stmt = Valways $ VAt ev $ VSeq body_items
    in
	VMStmt { vi_translate_off = False, vi_body = stmt }


-- generate an always block for all RegA on the same clock and reset
vInlineA :: VConvtOpts -> ((AExpr, AExpr), [AVInst]) -> VMItem
vInlineA vco ((clk, rstn), avis) =
    let
	-- create the conditional inside the always block
	-- (same body item as RegN!)
	body_item = translateRegN vco (rstn, avis)

	-- event for the surrounding always block
	ev = let v_rstn = vExpr vco rstn
		 v_clk  = vExpr vco clk
	     in  case (v_rstn) of
		     VEWConst _ _ _ v ->
		         if (v == 1)
			 then VEEposedge v_clk
			 else internalError
			          "vInlineA: unexpected constant rstn value"
		     _ -> VEEOr (VEEposedge v_clk) (mkEdgeReset v_rstn)

        -- this body has no begin/end because it is an if-stmt;
	stmt = 	Valways $ VAt ev $ body_item
    in
	VMStmt { vi_translate_off = False, vi_body = stmt }


-- Assign an initial (debug) value to all RegUN
mkInitialAssignments :: Flags -> [AVInst] -> [VMItem]
mkInitialAssignments flags [] = []
mkInitialAssignments flags avis =
    let
	-- make the assignment for one reg
        mkInit :: AVInst -> VStmt 
	mkInit avi =
	    let id = (mkQOUT avi)
		-- tag the VId with the instance that would have existed without inlining.
                -- XXX we pass in an empty rewiring map because registers have no inouts
		(_, vminst, _) = vState flags M.empty avi
		qout = VLId (VId (getIdString id) id (Just vminst))
		val = case (getRegWidth avi) of
			ASInt { ae_ival = IntLit { ilValue = width } }
			  -> let val = aaaa width
				 -- XXX use the ASInt ae_objid?
				 id = mkVId (itos val)
			     in  VEWConst id width 16 val
			e -> internalError ("mkInit: " ++ ppDebug e)
	    in  VAssign qout val

	-- use VSeq (not vSeq) so that the initial block always has
	-- begin/end, even when there is only one item inside it
	stmt = Vinitial $ VSeq $ map mkInit avis
    in
        [VMStmt { vi_translate_off = True, vi_body = stmt }]


-- make the conditional enable assignment to a register
mkENAssignment avi =
    let en = VEVar (vId (mkEN avi))
	qout = VLId (vId (mkQOUT avi))
	din = VEVar (vId (mkDIN avi))
    in
	Vif en (VAssignA qout din)

-- make the assignment on reset (to be put inside a conditional)
mkRSTAssignment vco avi =
    let qout = VLId (vId (mkQOUT avi))
	init_val = vExpr vco (getRegInit avi)
    in
	VAssignA qout init_val

translateRegN :: VConvtOpts -> (AExpr, [AVInst]) -> VStmt
translateRegN vco (rstn, avis) =
    let
	-- the assignments on reset
	rstn_items = map (mkRSTAssignment vco) avis

	-- the assignments on enable
	en_items = map mkENAssignment avis

	-- RST == `BSV_RESET_VALUE
	v_rstn = vExpr vco rstn
	v_rst = mkEqualsReset v_rstn
    in
	case (v_rstn) of
	    VEWConst _ _ _ v ->
	        if (v == 1)
		then vSeq en_items
		else internalError
		         "translateRegN: unexpected constant rstn value"
	    _ -> Vifelse v_rst (vSeq rstn_items) (vSeq en_items)

translateRegUN :: VConvtOpts -> AVInst -> VStmt
translateRegUN vco avi = mkENAssignment avi


-- ==============================
-- partition reg instances by their clock

partitionByClock :: ErrorHandle -> [AVInst] -> M.Map AExpr [AVInst]
partitionByClock errh avis =
    let mkPair avi = (getRegClock errh avi, [avi])
    in  M.fromListWith (flip (++)) (map mkPair avis)


-- ==============================
-- partition reg instances by their reset

partitionByReset :: ErrorHandle -> [AVInst] -> M.Map AExpr [AVInst]
partitionByReset errh avis =
    let mkPair avi = (getRegReset errh avi, [avi])
    in  M.fromListWith (flip (++)) (map mkPair avis)


-- ==============================
-- partition reg instances by their clock and reset (for RegA)

partitionByClockAndReset :: ErrorHandle -> [AVInst] -> M.Map (AExpr, AExpr) [AVInst]
partitionByClockAndReset errh avis =
    let mkPair avi = let clk_rst = (getRegClock errh avi, getRegReset errh avi)
                     in  (clk_rst, [avi])
    in  M.fromListWith (flip (++)) (map mkPair avis)


-- ==============================

