module AExpand (
                aExpand,
                aRemoveUnused, aSRemoveUnused, xaSRemoveUnused,
                xaXExpand,
                expandAPackage
                ) where

import Data.List(group, sort, nub, genericLength)
import qualified Data.Map as M
import qualified Data.Set as S
import PFPrint
import Position(noPosition)
import SCC
import Error(internalError, ErrMsg(..), ErrorHandle, bsErrorUnsafe)
import Id
import Prim
import ASyntax
import ASyntaxUtil
import VModInfo
import AConv(isLocalAId)
--import Util(traces)
--import Debug.Trace

-- ==============================
-- Static inputs to the expand function

type  ExpandTest a2 = ExpandData a2 -> AId -> AExpr -> Bool

data ExpandData a2 = ExpandData{
                             skeepFire :: Bool,
                             sexpnond  :: Bool,
                             sexpcheap :: Bool,
                             suses     :: M.Map Id Int,
                             skeeps    :: S.Set Id,
                             sss       :: [AVInst],
                             sws       :: [AId],
                             sfs       :: a2,
                             -- test function for expansion
                             sexpandTest :: ExpandTest a2
}


-- ==============================
-- Functions: aExpand, aXExpand, xaXExpand

-- Inline some definitions into other definitions, the submodule
-- instantiations, and foreign function calls, based on some
-- heuristics (see aExpDefs for details).  In this process, remove any
-- definitions which are not used, but keep some types of definitions
-- (again, see aExpDefs).

-- Finally, aSRemoveUnused and xASRemoveUnused are used to make sure
-- that unused definitions are removed, though some types of
-- definitions are kept.  (aExpand and aXExpand only remove unused
-- "_d" definitions, while xaXExpand can remove any unused
-- definition.)

-- XXX Can aExpand, aXExpand, and xaXExpand be merged into one?
-- XXX aExpand and aXExpand are the same, and xaXExpand is slightly
-- XXX different in the way that it removes definitions.

-- The X versions were for when there was a recursive data structure
-- used in the Verilog back-end (at some point ASPackage became a
-- recursive structure) and these versions were need to expand on that
-- structure.  xaXExpand might have a been version for allowing
-- expansion from a point inside the recursive structure.


aExpand :: ErrorHandle -> Bool -> Bool -> Bool -> ASPackage -> ASPackage
aExpand errh keepFires expnond expcheap pkg =
    aSRemoveUnused keepFires
                   (expandASPackage errh keepFires expnond expcheap pkg)

xaXExpand :: ErrorHandle -> Bool -> Bool -> Bool -> ASPackage -> ASPackage
xaXExpand errh keepFires expnond expcheap pkg =
    xaSRemoveUnused keepFires
        (expandASPackage errh keepFires expnond expcheap pkg)


-- common core
expandASPackage :: ErrorHandle -> Bool -> Bool -> Bool -> ASPackage -> ASPackage
expandASPackage errh keepFires expnond expcheap pkg =
    let
        ss = aspkg_state_instances pkg
        ws = aspkg_inlined_ports pkg
        ds = aspkg_values pkg
        fs = aspkg_foreign_calls pkg
        sigInfo = aspkg_signal_info pkg
        os = aspkg_outputs pkg
        ios = aspkg_inouts pkg
        si = aspkg_signal_info pkg
        -- ok to inline the submodule enables, just not mux inputs
        muxes = aspsi_mux_selectors si ++
                aspsi_mux_values si

        (ss', ws', ds', fs') =
            -- trace ("aExpand " ++ ppReadable ds) $
            aExpDefs errh keepFires expnond expcheap aoptExpandTest
                     sigInfo os ios muxes (ss, ws, ds, fs)
    in
        pkg { aspkg_state_instances = ss',
              aspkg_inlined_ports = ws',
              aspkg_values = ds',
              aspkg_foreign_calls = fs' }


-- ==============================
-- Function: aExpDefs

-- aExpDefs acts on the "ss", "ds", and "fs" fields of the ASPackage.
--   ss :: [AVInst]       = state elements
--   ws :: [AId]          = ports of inlined modules (RWire)
--   ds :: [ADef]         = local definitions
--   fs :: [AForeignCall] = foreign function calls
-- It takes as input the schedule and the "os" (:: [AOutput] = ifc outputs)
-- aExpDefs does this:
-- (1) Find the variables that each definition (in "ds") uses.
-- (2) Make a list of the ids of the "ds".
-- (3) Find all the ids used by "ss", "ds", and "fs", and then zip them
--     with 1 or 2 depending on whether they are used 1 or multiple times
--     (and for uses in "ss" and "ws", always zip them with 2, because it's
--     more readable not to inline "ss" and aids debugging for "ws"),
--     and convert it into a map (for quick lookup).
-- (4) Produce a list of Ids to "keep".  This includes:
--        CAN_FIRE_ and WILL_FIRE signals,  (XXX which are re-made)
--        the outputs of the module ("os"),
--        and the definitions ("ds") which are state I/O
--        (XXX This is currently checked by looking for "$" in the name
--         XXX It should at least use ASyntax::isMethId)
-- (5) Create the ExpandData data structure with:
--        skeepFire = whether to preserve rule firing signals (keepFires flag)
--        sexpnond  = whether all defs can be considered for inlining
--                    not just defs with "bad" names
--                    (such defs used to start with "d", hence "expand non-d")
--        sexpcheap = whether "cheap" operations can be considered for inlining
--        suses  = the usemap from step 3 (a map to the rough number of uses)
--        skeeps = a list of Ids to keep (not inline)
--        sss    = ss
--        sws    = ws
--        sfs    = fs
-- (6) Make a graph of how the Ids in "ds" depend on each other, and tsort
--     to flatten it to a list.  If there are cycles, report an ECombCycle.
--     Otherwise, put "ds" in the flattened (dependency) order.
-- (7) Call "expand" on the ordered definitions, with the ExpandData


aExpDefs :: ErrorHandle -> Bool -> Bool -> Bool -> ExpandTest [AForeignBlock] ->
            ASPSignalInfo -> [AOutput] -> [AInput] -> [AId] ->
            ([AVInst], [AId], [ADef], [AForeignBlock]) ->
            ([AVInst], [AId], [ADef], [AForeignBlock])
aExpDefs errh keepFires expnond expcheap expTest sigInfo os ios muxes (ss', ws', ds', fs') =
    let
        usemap = createUseMap muxes (ss', ws', ds', fs')
        sorted_defs = tsortDefs errh ds'

        -- compute the signal names to keep
        keepSchIds = if ( keepFires) then concat $ map snd (aspsi_rule_sched sigInfo) else []
        -- this prevents AExpand from dropping WILL_FIRE and CAN_FIRE signals
        -- when their uses drop to 0
        -- keep sched ids, defs for module outputs, and submodule inputs
        -- XXX the us of isMethId should be conditional with the keep-inlined-boundaries flag.
        keepIds = keepSchIds ++
                  (map fst os) ++ (map fst ios) ++
                  [ i | ADef i _ _ _ <- ds', isMethId i || hasIdProp i IdP_keepEvenUnused ]

        edata = -- traces( "keepids: " ++ ppReadable keepIds ) $
                ExpandData { skeepFire = keepFires, sexpnond = expnond,
                             sexpcheap = expcheap, suses = usemap,
                             skeeps = (S.fromList keepIds),
                             sss = ss', sws = ws', sfs = fs',
                             sexpandTest = expTest}
    in
        -- traces ("keepIds=" ++ ppReadable keepIds
        --                    ++ "keep g " ++ ppReadable g
        --                    ++ "keep is " ++ ppReadable uses
        --                    ++ "keep defidss " ++ ppReadable (S.toList def_ids )
        --                    ++ "keep ds" ++ ppReadable ds'
        --                    ++ "keep schids" ++ ppReadable keepSchIds
        --       ) $
        -- do the expansion
        expand edata M.empty sorted_defs []


-- Topologically sort defs
tsortDefs :: ErrorHandle -> [ADef] -> [ADef]
tsortDefs errh ds = sorted_defs
  where
    -- compute the signal use edges for all defs
    uses :: [(AId,[AId])]
    uses = map (\ (ADef i _ e _) -> (i, aVars e)) ds
    --
    -- sort the ds into dependency order
    -- (tsort the ids and use a map of id-to-def to quickly convert
    --  the sorted ids back into sorted defs)
    def_ids :: S.Set AId -- the Ids which are defined on the LHS
    def_ids = S.fromList (map fst uses)
    g = [(i, nub (filter (`S.member` def_ids) is)) | (i, is) <- uses]
    sorted_def_ids =
        case tsort g of
        Left is ->
            bsErrorUnsafe errh
                [(noPosition, ECombCycle (map pfpString (concat is)))]
        Right is -> is
    omap = M.fromList [ (i, d) | d@(ADef i _ _ _) <- ds ]
    sorted_defs = map (getDef omap) sorted_def_ids


createUseMap ::  [AId] -> ([AVInst], [AId], [ADef], [AForeignBlock]) -> M.Map Id Int
createUseMap  muxes (ss', ws', ds', fs') = usemap
    where
        -- create a map from names to the number of uses
        -- (either not in the map, 1 for one use, or 2 for two or more uses)
        usemap = (M.fromList . map xLen . group . sort)
                     (aCollectUses ss' ws' muxes ds' fs')
        --
        xLen :: [a] -> (a, Int)
        xLen [i] = (i, 1)
        xLen (i:_) = (i, 2)
        xLen [] = internalError "AExpand.createUsemap::xlen []"


-- ==============================
-- Function: aSRemoveUnused

-- asRemoveUnused updates the definitions in the ASPackage ("ds")
-- to remove any local defs (those starting with "_d") which are not
-- depended on by the expressions in non-local defs, submodule
-- instantiations ("ss"), or foreign function calls ("fs").

-- An expression depends on a definition if the def's Id appears
-- directly in the expression or if the Id appears in a definition on
-- which the expression depends.


aSRemoveUnused :: Bool -> ASPackage -> ASPackage
aSRemoveUnused keepfires pkg =
    let ds = aspkg_values pkg
        vused = aVars (aspkg_state_instances pkg)
        fused = aVars (aspkg_foreign_calls pkg) ++
                (concat [ afc_writes fc
                        | (_,fcs) <- aspkg_foreign_calls pkg
                        , fc <- fcs ])
        fires = if keepfires then [i | (ADef i _t _e _) <- ds, isFire i] else []
        ds' = (collDefs (vused ++ fused ++ fires ) ds)
    in
        -- trace ("aSRemoveUnused \nds = " ++ ppReadable ds ++
        --        "\n ds' = " ++ ppReadable ds') $
        --traces( "aSRemoveUnused : old defs: " ++ ppReadable ds ) $
        --traces( "aSRemoveUnused : new defs: " ++ ppReadable ds' ) $
        pkg { aspkg_values = ds' }


-- ==============================
-- Function: aRemoveUnused
--     (used only by AExpandP and CCExpand)

-- Like aRemoveUnused, but for APackage instead of ASPackage:
-- aRemoveUnused removes local defs (those starting with "_d") which
-- are not needed to define any non-local defs or any local defs used
-- in state instances, rules, or methods.


aRemoveUnused :: APackage -> APackage
aRemoveUnused apkg =
--    trace ("aRemoveUnused:\n   vused " ++ ppReadable vused
--    ++ "\n   rused: " ++ ppReadable rused
--    ++ "\n   iused: " ++ ppReadable iused) $
        apkg { apkg_local_defs = ds' }
  where ds' = collDefs (vused ++ rused ++ iused) (apkg_local_defs apkg)
        vused = aVars (apkg_state_instances apkg)
        rused = aVars (apkg_rules apkg)
        iused = aVars (apkg_interface apkg)


-- ==============================
-- Function: collDefs

-- collDefs takes a list of Ids which are used in the package and the
-- definitions from the package, and it drops any local definitions
-- (those starting with "_d") which are unnecessary -- necessary
-- definitions are those for the used Ids and for any Ids in the
-- definitions of the used Ids (recursively).

-- By sorting the defs in dependency order, and considering them in
-- reverse, when the "coll" function decides to keep a def, it can add
-- the vars of that def to the "used" list and be confident that the
-- defs for those ids are still come in the defs being considered.


-- collect used definitions (and everything they use)
collDefs :: [AId] -> [ADef] -> [ADef]
collDefs used ds = coll (S.fromList used) [] (reverse (tsortADefs ds))
  where coll _    rs [] = rs
        coll used rs (d@(ADef i _ e _) : ds) =
                if isLocalAId i
                   && not (isKeepId i)
                   && not (S.member i used) then
                    --traces ("drop-coll " ++ ppString i) $
                    coll used rs ds
                else
                    coll (foldr S.insert used (aVars e)) (d:rs) ds


-- ==============================
-- Function: xaSRemoveUnused

-- xasRemoveUnused updates the definitions in the ASPackage ("ds")
-- to remove any defs (not just "_d" ones) which are not needed by
-- other parts of the ASPackage:
--    the state I/O ("os"),
--    any Ids used in the foreign function calls ("fs"),
--    any vars used in the submodule instantiation ("ss"), and
--    the "stArgs" of the submodule instantiations
--    (the names of signals attached to submodule input ports)
--
-- The definitions ("ds") of the package are then filtered to keep only
-- the definitions which are needed to define these Ids.

-- Note that the list "ws" (inlined RWire ports) are fair game to be
-- removed.  This is what distinguishes that list from true "keep" signals.
-- XXX Also note that those removed signals are not removed from "ws".

-- XXX stArgs creates new names for the method ports!
-- XXX We shouldn't duplicate this work! It should either already be
-- XXX computed, or there should be standardized functions for getting
-- XXX the values.

-- Is there a difference between xaSRemoveUnused and aSRemoveUnused?
--   Yes, aSRemoveUnused only removes unused local Ids, while
--   xaSRemoveUnused uses xcollDefs which can remove anything, so it
--   is necessary (it seems) to include many more names in the "used"
--   list.  Plus, xaSRemoveUnused takes keepFires as an argument.


xaSRemoveUnused :: Bool -> ASPackage -> ASPackage
xaSRemoveUnused keepFires pkg =
    -- trace ("xaSremoveUNused \nds = " ++ ppReadable ds ++
    --        "\n ds' = " ++ ppReadable ds' ++ "\n os = " ++ ppReadable os) $
    pkg { aspkg_values = ds' }
  where
        ds = aspkg_values pkg
        ss = aspkg_state_instances pkg
        vused = aVars ss ++ concatMap stArgs ss
        -- XXX the us of isMethId should be conditional with the keep-inlined-boundaries flag.
        oused = map fst (aspkg_outputs pkg)
                ++ map fst (aspkg_inouts pkg)
                ++ [ i | (ADef i _t _e _) <- ds, isMethId i ||  isFire i && keepFires]
        fused = aVars (aspkg_foreign_calls pkg) ++
                (concat [ afc_writes fc
                        | (_,fcs) <- aspkg_foreign_calls pkg
                        , fc <- fcs ])
        --
        ds' = --traces("xasRemovedUnused oused: " ++ ppReadable oused ) $
              --traces("xasRemovedUnused fused: " ++ ppReadable fused ) $
              --traces("xasRemovedUnused vused: " ++ ppReadable vused ) $
              --traces("xasRemovedUnused defs: " ++ ppReadable ds ) $
              xcollDefs keepFires (vused ++ oused ++ fused) ds
        --

        stArgs :: AVInst -> [AId]
        stArgs (AVInst { avi_vname = v, avi_vmi = vi }) =
            concatMap (mkMethInputIds v) (vFields vi)

        -- construct the method syntax ids for enable and argument inputs
        mkMethInputIds :: AId -> VFieldInfo -> [AId]
        mkMethInputIds v m@(Method {vf_name = i, vf_mult = mult}) =
            let en = case (vf_enable m) of
                         Nothing -> []
                         Just _ -> [MethodEnable]
                args = map MethodArg [1..genericLength (vf_inputs m)]
            in  [ mkMethId v i ino part |
                  part <- en ++ args, ino <- if mult > 1
                                             then map Just [0 .. mult-1]
                                             else [Nothing]
                ]
        mkMethInputIds v (Clock i) = []
        mkMethInputIds v (Reset i) = []
        mkMethInputIds v (Inout {}) = []


-- ==============================
-- Function: xcollDefs

-- This is an AX-version of collDefs (from when there was an AXSyntax).

-- Is there a difference between xcollDefs/collDefs?
--  * collDefs checks for isLocalAId (which is defined by AConv as
--    starting with "_d") and automatically keeps all other defs
--  * xcollDefs does no checks (and thus all defs are fair game to be
--    dropped), but it takes keepFires as an argument and checks for
--    "(not keepFires) || (not (isFire i))" so as not to remove rule
--    firing signals when the -keep-fires flag is on.
--

xcollDefs :: Bool -> [AId] -> [ADef] -> [ADef]
xcollDefs keepFires used ds = --traces( "xCollDefs: " ++ ppReadable used ) $
                              coll (S.fromList used) [] (reverse (tsortADefs ds))
  where coll _    rs [] = rs
        coll used rs (d@(ADef i _ e _) : ds) =
            if (((not keepFires)  || (not (isFire i)))
                && (not (S.member i used))
                && (not (hasIdProp i IdP_keepEvenUnused))
               ) then
                --traces ("\n drop-coll " ++ ppString i ++ " " ++ ppReadable (hasIdProp i IdPCanFire)) $
                coll used rs ds
                else
                    coll (foldr S.insert used (aVars e)) (d:rs) ds


-- ==============================
-- Function: aCollectUses

-- aCollectUses takes the "ss", "ws", "ds", and "fs" and returns a
-- list of the Ids which they refer to.  It also puts uses in "ss" and
-- "ws" in the list twice ... to prevent them from being inlined
-- (because it avoids errors for "ss", and aids debugging for "ws"),
-- by guaranteeing that the variables appear to be used more than once
-- so that the heuristic of inlining of single-use variables doesn't
-- touch them.  This should be done in a better way (though it's only
-- used by aExpDefs).

aCollectUses :: [AVInst] -> [AId] -> [AId] -> [ADef] -> [AForeignBlock] -> [AId]
aCollectUses ss ws muxes ds fs =
    let uses = aVars ds
        vuse = ws ++ muxes ++ aVars ss
        fuse = aVars fs ++ (concat [afc_writes fc | (_,fcs) <- fs, fc <- fcs])
        -- Pretend variables in instances and rwire ports are used
        -- twice so they don't get inlined.
        -- This makes it more readable and easier to transform.
        vuse2 = vuse ++ vuse
    in  uses ++ vuse2 ++ fuse


-- ==============================
-- Function: isSimple

-- isSimple is used by "expand" to decide what to inline.  It takes a
-- Bool indicating whether to inline cheap operations.
--
--  * A Primitive is simple if cheap inlining is turned on, the
--    primitive is cheap (see below), and all of the arguments to the
--    primitive are simple.
--  * A method call is simple if and only if it has no arguments.
--  * A foreign function call that is imported from C must not be inlined.
--  * A foreign function call with no ports (thus, a system task) is
--    simple.  A foreign function call with ports is a module
--    instantiation, and thus cannot be inlined.
--  * Tasks are not inlined.
--  * Everything else is inlineable.
-- Some APrim things are always e.g.: simple NOT, Extract of const,  EQ to const,

isSimple :: Bool -> AExpr -> Bool
isSimple c (APrim i t PrimExtract [ e , (ASInt{} ), (ASInt {} )]) = isSimple c e
isSimple c (APrim i t PrimBNot [e])                               = isSimple c e
isSimple c (APrim i t PrimInv [e])                                = isSimple c e
isSimple _ (APrim i t PrimEQ  [_, (ASInt _ (ATBit sz) _)])        = True
isSimple c (APrim i t PrimConcat es)                              = c && all (isSimple c) es
isSimple c e@(APrim _ _ p es)                                     = c && isSmall e && cheap p es -- && all (isSimple c) es
isSimple c (AMethCall _ _ _ es)                                   = null es
isSimple c (AMethValue _ _ _)                                     = True
isSimple c (ATupleSel _ e _)                                      = isSimple c e
isSimple c (ATuple _ es)                                          = all (isSimple c) es
-- foreign function calls cannot be inlined
-- (except for $signed and $unsigned - handled by mustInline)
isSimple c e@(AFunCall { })                                       = False
-- function calls which are module instantiations cannot be inlined
isSimple c (ANoInlineFunCall { })                                 = False
-- ATaskValue must NOT be inlined
isSimple c (ATaskValue { })     = False
isSimple c (ASInt _ _ _)        = True
isSimple c (ASDef _ _)          = True
isSimple c (ASPort _ _)         = True
isSimple c (ASParam _ _)        = True
isSimple c (ASReal _ _ _)       = True
isSimple c (ASStr _ _ _)        = True
isSimple c (ASAny _ _)          = True
isSimple c (ASClock { })        = internalError("AExpand.isSimple ASClock unexpected")
isSimple c (ASReset { })        = internalError("AExpand.isSimple ASReset unexpected")
isSimple c (ASInout { })        = internalError("AExpand.isSimple ASInout unexpected")
isSimple c (AMGate { })         = True


-- ==============================
-- Function: cheap

-- "cheap" determines whether a primitive is cheap (for inlining).
--  * NOT is cheap
--  * AND and OR are cheap if they have less than 9 arguments
--  * EQ is cheap if comparison with a constant of size less than 24
--    -- it is needed for AOpt::aInsertCase
--  * Bit extraction is cheap -- no logic overhead
--  * Everything else is not cheap


cheap :: PrimOp -> [AExpr] -> Bool
cheap PrimBNot es                                = True
cheap PrimBAnd es                                = length es < 9
cheap PrimBOr  es                                = length es < 9
cheap PrimEQ   [_, (ASInt _ (ATBit sz) _)]       = sz <= 24             -- comparing with a small constant is easy
cheap PrimExtract [ _ , (ASInt{} ), (ASInt {} )] = True
cheap _        es                                = False


-- this is heuristic to determine is an expression is small
-- for some definition of small
isSmall :: AExpr -> Bool
isSmall e = or [
                length vars <= 2, -- if there is only 2 vars, then it is small
                                  -- consder a==1 && a==2 && a==3, etc.
                depth <= 2 && terms <= 4, -- just a weird idea -- short but fat
                length vars <= 3 && terms <= 8 && depth <= 4 -- and yet another one for b292
                ,length vars <= 4 && terms <= 6 && depth <= 3 -- shorter and fatter
               ]
    where (vars,terms,depth) = getExprSize e

-----------------------------------------------------------------

-- get the size -- number of terms, and the depth of the expression
-- useful to measure a expression for isSimple
getExprSize :: AExpr -> ([AId],Int,Int)

-- consider some logic operation as having no cost.  x  and !x,  e[const]
getExprSize (APrim _ _ PrimBNot [e]) = getExprSize e
getExprSize (APrim _ _ PrimInv  [e]) = getExprSize e
getExprSize (APrim i t PrimEQ  [el, (ASInt _ (ATBit sz) _)]) = getExprSize el
getExprSize (APrim i t PrimExtract [ el , (ASInt{} ), (ASInt {} )]) = getExprSize el

-- PrimIf adds 2 to the maximum of its arguments
getExprSize (APrim i t PrimIf es) = (nub $ concat vars, sum terms, 2 + maximum depths)
    where (vars,terms,depths) = unzip3 $ map getExprSize es

-- These don't need to be specially handled, because they are not inlineable
--getExprSize (APrim _ _ PrimBuildArray es) =
--getExprSize (APrim _ _ PrimArrayDynSelect es) = ...

-- all other primitives add 1 to the max of its arguments
getExprSize (APrim _ _ _ es) = (nub $ concat vars, sum terms, 1 + maximum depths)
    where (vars,terms,depths) = unzip3 $ map getExprSize es

getExprSize (AMethCall t i mid args) = ([mid],1,1)
getExprSize (AMethValue t i mid)     = ([mid],1,1)
getExprSize (ATupleSel t e i)        = (vars, terms + 1, depth + 1)
    where (vars,terms,depth) = getExprSize e
getExprSize (ATuple t es)            = (nub $ concat vars, sum terms + 1, maximum depths + 1)
    where (vars,terms,depths) = unzip3 $ map getExprSize es
getExprSize (ATaskValue { })         = ([],   1,1)
getExprSize (ASPort t i)             = ([i],  1,1)
getExprSize (ASParam t i)            = ([i],  1,1)
getExprSize (ASInt {} )              = ([],   0,1)
getExprSize (ASDef t i)              = ([i],  1,1)
getExprSize (ASReal {})              = ([],   0,1)
getExprSize (ASStr {})               = ([],   0,1)
getExprSize (ASAny {})               = ([],   0,1)
getExprSize (ANoInlineFunCall { })   = ([],   1,1)
getExprSize (AFunCall { })           = ([],   1,1)
getExprSize (ASClock {} )            = ([],   1,1)
getExprSize (ASReset {} )            = ([],   1,1)
getExprSize (ASInout {} )            = ([],   1,1)
getExprSize (AMGate t i c)           = ([c],  1,1) -- XXX ? c is not unique to the gate?


-- ==============================
-- Function: getUses

-- getUses is used on the number-of-uses map, which maps an Id to
-- either 1 or 2, depending on whether it is used once or many times.
-- If the Id to be looked up is not in the map, then getUses returns 0.

getUses :: M.Map Id Int -> Id -> Int
getUses m i = M.findWithDefault 0 i m


-- ==============================
-- Function: getDef

getDef :: M.Map Id ADef -> Id -> ADef
getDef m i =
    M.findWithDefault (internalError ("AExpand.getDef " ++ ppString i)) i m


-- ==============================
-- Function: inlineable

-- "inlineable" is another test for whether to inline an expression or not
-- (even if it is "simple"!)
--
--  * A TaskValue should not be inlined because it exists to grab a name
--    for the corresponding system task call to when Verilog is generated
--  * Foreign function calls are not inlineable (except for the cases in mustInline)
--  * NoInline module function calls are not inlineable
--  * A method call cannot be inlined
--  * A Mux or PriMux primitive cannot be inlined
--  * PrimArrayDynSelect is not inlined, because we always want it to be
--    converted to a case (which only happens for defs)
--  * Everything else can be inlined


inlineable :: AExpr -> Bool
-- the only inlineable foreign function calls are
-- $signed and $unsigned (handled by inlineable)
inlineable e@(AFunCall {}) = False
-- never inline an ATaskValue it is just an assignment:
inlineable (ATaskValue { }) = False
-- never inline foreign call, it needs a named result:
inlineable (ANoInlineFunCall { }) = False
inlineable (AMethCall { }) = False
inlineable (AMethValue { }) = False
inlineable (AMGate { }) = False  -- treat like a method call
inlineable (APrim _ _ PrimMux _) = False
inlineable (APrim _ _ PrimPriMux _) = False
inlineable (APrim _ _ PrimMul _) = False -- XXX EWC is this good?
inlineable (APrim _ _ PrimQuot _) = False
inlineable (APrim _ _ PrimRem _) = False
-- never inline an an array selection (it will need to become a case-stmt)
inlineable (APrim _ _ PrimArrayDynSelect _) = False
-- anything else:
inlineable _ = True


-- Function: mustInline
-- These are expressions that are required to be inlined regardless of
-- other heuristics
-- There are two kinds of such expressions:
--  - String expressions
--     (conditional muxes involving strings must be unfolded in veriquirks)
--     XXX: If we allow foreign functions returning strings we'll have to be
--          more careful here
--  - $signed and $unsigned
--    (since they only work if inlined into the appropriate system task call)

mustInline :: AExpr -> Bool
mustInline (AFunCall {ae_funname = n }) = n `elem` ["$signed", "$unsigned"]
mustInline e = isStringType (aType e)

-- ==============================
-- Function: expand

-- the core expander loop (called by aExpDefs)

-- "expand" takes the ExpandData structure and a list of definitions (in
-- dependency order) and it returns the updated submodule instantiations,
-- list of definitions, and foreign function calls (ss', ds', fs').

-- The computation is done recursively, by starting with two empty
-- maps -- a map of Ids to the expressions which should replace them
-- (when inlining)
-- and an empty list "nds" which will become the new
-- definitions (thus "nds").

-- For each definition "i" which is considered,
--  * if the number of uses is zero and it is not in the keep list,
--    then the definition is added to the "nds", but with any inlined
--    Ids substituted into the definition.
--  * if the Id is to be inlined, then it is added to the map.  An Id
--    is inlined if it is a local Id (starts with "_d") or if the
--    expandATSdef flag is on (in which case all Ids are fair game) and
--    it is not a rule firing signal (unless keepFires is off) and it is
--    inlineable (according to the function "inlineable") and either it
--    is only used in one place or it is a simple expression (according
--    to the function "isSimple", applied to the expression with inlined
--    definitions substituted in).

-- When all definitions have been considered, it returns:
--  * the list of AVInst ("ss") with inlining applied to the "es" of
--    the instantiation.
--  * the list of definitions, in dependency order (thus the call to
--    "reverse" after compiling the "nds")
--  * the list of foreign function calls ("fs") with inlining applied
--    to the "es"


expand :: (AExprs e2, PPrint e2) =>  ExpandData e2 -> (EMap AExpr) -> [ADef] -> [ADef]
       -> ([AVInst], [AId], [ADef], e2)

-- the end condition for the loop:
-- we are done, so just substitute through the new definitions
-- in the state variable instances and the foreign function calls
expand  edata edefs [] nds =
        (aSubst edefs ss,
         ws,
         reverse nds,
         aSubst edefs fs)
    where
      fs = sfs edata
      ss = sss edata
      ws = sws edata

-- the loop: consider the top definition and recurse on the rest
expand edata edefs (ADef i t e ps : ds) nds =
        let
            uses      = suses edata
            keep      = skeeps edata
            --
            -- substitute all the good subs up to now.
            e' = aSubst edefs e
            nuse = getUses uses i

            -- build list of new definitions
            nds' = if nuse == 0 && not (S.member i keep)
               then nds
                else ADef i t e' ps : nds

            doExpand = (sexpandTest edata) edata i e'

            -- create the new map here
            edefs' = if doExpand then
                         M.insert i e' edefs
                     else
                         edefs
        in
            expand edata edefs' ds nds'

-- Tests on AId and AExpr to determine if the expression should be inlined during aOpt
-- Based on number of heuristics which are good for synthesis.
aoptExpandTest :: ExpandData e2 -> AId -> AExpr -> Bool
aoptExpandTest edata i e =
  let keepFires = skeepFire edata
      expnond   = sexpnond edata
      expcheap  = sexpcheap edata
      uses      = suses edata
      nuse      = getUses uses i
      instVars  = aVars (sss edata)
  in  ((expnond || isLocalAId i) &&
       ((not keepFires) || (not (isFire i))) &&
       (not (isKeepId i)) &&
       inlineable e &&
       ((nuse > 0 && isSimple expcheap e) || ((nuse == 1) && (isSmall e))) &&
       (isConst e || not (i `elem` instVars)) ||
       mustInline e
       )


-- SERI version
expandAPackage :: ErrorHandle -> APackage -> APackage
expandAPackage errh apkg = apkgN
    where sorted_defs = tsortDefs errh (apkg_local_defs apkg)
          -- generate a always used def map, since predicates are not yet generated
          usemap = M.fromList ([ (i,2) | (ADef i _ _ _) <- sorted_defs])
          --
          edata = ExpandData {
            skeepFire = False   -- Not present
            ,sexpnond = False -- not used
            ,sexpcheap = True -- not used
            ,suses = usemap
            ,skeeps = (S.empty)
            ,sss = []    -- not used
            ,sws = []   -- not used
            ,sfs = ((apkg_rules apkg), (apkg_interface apkg))
            ,sexpandTest = aSeriExpandTest
            }
          --
          -- do the expansion
          (_,_, defs, (rules,ifc)) = expand edata M.empty sorted_defs []
          -- rebuild the package
          apkgN = aRemoveUnused $ apkg { apkg_local_defs = defs,
                                         apkg_rules = rules,
                                         apkg_interface = ifc}


-- Tests on AId and AExpr to determine if the expression should be inlined during aOpt
-- Based on number of heuristics which are good for synthesis.
aSeriExpandTest :: ExpandData a -> AId -> AExpr -> Bool
aSeriExpandTest _ i e = isSeriInline e

-- For Seri dumps we want to inline extract and Not
isSeriInline :: AExpr -> Bool
isSeriInline (APrim i t PrimExtract [ e , (ASInt{} ), (ASInt {} )]) = True
isSeriInline (APrim i t PrimBNot [e])                               = True
isSeriInline (APrim i t PrimConcat es)                              = True
isSeriInline (APrim i t PrimChr es)                                 = True
-- Method calls can't be inlined into the arguments of actions, because this
-- causes trouble for the routine that sorts defs/action in a rule (given its
-- current assumptions).  Simplest thing is to not inline method calls;
-- although this is conservative.  We could allow inlining here, but filter
-- out defs containing method calls when we apply aSubst to the actions.
--isSeriInline (AMethCall _ _ _ es)                                   = null es
-- isSeriInline (AMethValue _ _ _)                                     = True
isSeriInline _ = False
