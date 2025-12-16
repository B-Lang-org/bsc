module VIOProps (VIOProps, getIOProps) where

import Data.List(intersect)
import Data.Maybe(catMaybes, isNothing)
import qualified Data.Map as M
import qualified Data.Set as S
import Util
import Eval(NFData(..), rnf)
import Flags
import PPrint
import ErrorUtil(internalError)
import Id
import PreIds(idPrimAction, idInout_)
import VModInfo(vArgs, vFields, VName(..), VeriPortProp(..),
                VArgInfo(..), VFieldInfo(..), VPort)
import Prim
import ASyntax
import ASyntaxUtil( AVars(..) )
import BackendNamingConventions(createVerilogNameMapForAVInst,
                                xLateIdUsingFStringMap)

-- import Debug.Trace
-- import Util(traces)


-- The VIO properties are best described as the comments which are printed
-- before the verilog module is dumped in the Verilog file..

data IOIO = INPUT | OUTPUT | INOUT deriving (Eq)

instance NFData IOIO where rnf x = seq x ()

--   (name, input(T)/output(F), width, properties)
newtype VIOProps = VIOProps [(AId, IOIO, Integer, [VeriPortProp])]
        deriving (Eq)

instance NFData VIOProps where
    rnf (VIOProps xs) = rnf xs

instance PPrint VIOProps where
    pPrint d p (VIOProps ps) =
                text "Name                         I/O  size props" $+$
                foldr ($+$) (text "") (map pp ps)
        where pp (i, io, sz, ps) =
                let s = getIdString i
                    si = s ++ replicate (29 - length s) ' '
                    n = itos sz
                    sn = replicate (5 - length n) ' ' ++ n
                    iotxt = case (io) of
                              INPUT -> " I"
                              OUTPUT-> " O"
                              INOUT -> "IO"
                in  text si <+> text iotxt <+>
                    text sn <+> sep (map (pPrint d 0) ps)

-- assuming foreign functions do not affect the IO properties
getIOProps :: Flags -> ASPackage -> (VIOProps, [VPort])
getIOProps flags ppp@(ASPackage _ _ _ os is ios vs _ ds io_ds fs _ _ _) =
        -- returns the VIOProps structure
        -- and a mapping of Verilog port names to their port properties
        (VIOProps ais, [(VName (getIdString i), ps) | (i, _, _, ps) <- ais ])
  where
        -- VIOProps for all outputs
        ois = map getOInfo os
        -- VIOProps for all inputs
        iis = map getIInfo is
        -- VIOProps for all inouts
        iois = map getIOInfo ios
        -- VIOProps for all ports (but only nonzero sized)
        ais = filter nonZero (ois ++ iis ++ iois)
                where nonZero (_, _, sz, _) = sz /= 0

        -- construct VIOProps for an output
        getOInfo :: (AId,AType) -> (AId, IOIO, Integer, [VeriPortProp])
        getOInfo (i, t) = (i, OUTPUT, size t, getOProp i)

        -- construct VIOProps for an input
        getIInfo :: (AId,AType) -> (AId, IOIO, Integer, [VeriPortProp])
        getIInfo (i, t) = (i, INPUT, size t, getIProp i)

        -- construct VIOProps for an inout
        getIOInfo :: (AId,AType) -> (AId, IOIO, Integer, [VeriPortProp])
        getIOInfo (i, t) = (i, INOUT, size t, getIOProp i)

        -- lookup the definition for an id
        getDef :: AId -> ADef
        getDef i = M.findWithDefault err i defMap
            where err = internalError ("getIOProps.getDef failed: " ++
                                       ppString (i, defMap))

        -- mapping from ids to their defs
        defMap = M.union (M.fromList [(i, d) | d@(ADef i _ _ _) <- ds ])
                         -- XXX do the two maps ever mix?  can we defined
                         -- XXX getIOProps to only work with the ioDefMap?
                         ioDefMap

        ioDefMap = M.fromList [(i, d) | d@(ADef i _ _ _) <- io_ds ]

        -- ----------
        -- construct the VeriPortProp list for an output

        getOProp i =
            case getDef i of
            ADef _ _ e _ -> let deduced_props = getOEP e
                            in  -- we could add any props known the ifc here
                              -- (such as input clocks/resets)
                              -- for now, we just derive this
                              -- (but it means that "const" outputs don't
                              -- also get props like "reset" or "gate")
                              deduced_props

        -- given the props for multiple signals,
        -- compute the props that the concatenation should have
        joinOutProps :: [[VeriPortProp]] -> [VeriPortProp]
        joinOutProps (x:xs) = foldr intersect x xs
        -- empty list only occurs with prims of no args
        -- XXX do we have any? if they all give constant return values,
        -- XXX then we could return [VPconst] here
        joinOutProps [] = []

        -- construct the VeriPortProp list for an expression
        getOEP :: AExpr -> [VeriPortProp]
        -- for concats, find the common properties of the pieces
        getOEP (APrim _ _ PrimConcat es)         = joinOutProps (map getOEP es)
        -- an extraction doesn't change the properties
        getOEP (APrim _ _ PrimExtract [e, _, _]) = getOEP e
        -- either an output port of a submodule or an input to the ASPackage
        -- (so get its properties)
        getOEP (ASPort _ i)                      = getOVProp i
        -- follow defs
        getOEP (ASDef _ i)                       = getOProp i
        -- constant values
        getOEP (ASParam _ i)                     = [VPconst]
        getOEP (ASInt _ _ _)                     = [VPconst]
        getOEP (ASStr _ _ _)                     = [VPconst]
        -- for any other use, we cannot conclude properties
        getOEP _                                 = []

        -- build table of wire properties for the state element outputs
        wireMap_out :: M.Map AId [VeriPortProp]
        wireMap_out =
            let submod_pairs =
                    -- clock and reset outputs
                    [(i, ps) |
                         v <- vs,
                         (i, _, (_, ps)) <- getSpecialOutputs v] ++
                    -- output ports for method return values
                    [(veri_id, pprops) |
                         -- for each instance
                         v <- vs,
                         -- create the method name map
                         let nmap = M.fromList $
                                    createVerilogNameMapForAVInst flags v,
                         -- for each method that has an output port
                         vfi@(Method { vf_output = Just (vname,pprops) })
                             <- vFields (avi_vmi v),
                         -- for each port copy
                         ino <- if (vf_mult vfi > 1) then
                                  map Just [0 .. vf_mult vfi]
                                else [Nothing],
                         -- construct the method output signal name
                         let meth_id = mkMethId (avi_vname v)
                                                (vf_name vfi)
                                                ino
                                                MethodResult,
                         -- convert to Verilog signal name
                         let veri_id = xLateIdUsingFStringMap nmap meth_id
                    ]
                -- outputs can also come from top-level inputs;
                -- we use [] for the properties of the input
                -- XXX this should be OK, because the deriving of the
                -- XXX property for the input would give up if it
                -- XXX reached an output, and the props would be []
                input_pairs =
                    [ (i, []) | (i,_) <- is ]
                -- ifc inouts can also come from argument inouts
                inout_pairs =
                    [ (i, [VPinout])
                      | (i,_) <- ios,
                        isNothing (M.lookup i ioDefMap) ]
            in
                M.unions [M.fromList submod_pairs,
                          M.fromList input_pairs,
                          M.fromList inout_pairs]

        getOVProp :: AId -> [VeriPortProp]
        getOVProp i =
            case (M.lookup i wireMap_out) of
                Just ps -> ps
                Nothing ->
                    -- since we added the module inputs to the map,
                    -- this branch should never happen.  alternatively,
                    -- we could not put the inputs in the map and just
                    -- return empty-list here; but the internal check
                    -- is nice to have (if it's not too expensive).
                    internalError ("getOVProp: could not find method " ++
                                   ppString i)

        -- ----------
        -- construct the VeriPortProp list for an input

        getIProp :: AId -> [VeriPortProp]
        getIProp i =
            let derived_props = getSignalInProp i
            in  -- we could add any props known from the ifc here
                -- (such as input clocks/resets)
                -- for now, we just derive this (see comment below)
                derived_props

        -- given the deduced props for multiple signals,
        -- compute the props that should be deduced for a signal
        -- which connects directly to all these signals (and only these)
        joinInProps :: [[VeriPortProp]] -> [VeriPortProp]
        joinInProps pss =
            let
                -- if a signal is unused, it might as well not exist,
                -- so don't count it
                pss' = filter (VPunused `notElem`) pss
            in
                case pss' of
                    [] -> [VPunused]
                    (x:xs) ->
                        -- otherwise, a prop needs to be on all used signals
                        -- for it to be on the source
                        foldr intersect x xs

        -- a list the signals which are connected to
        -- submodule input ports (method arguments and enables)
        wireMap_in :: M.Map Id [VeriPortProp]
        wireMap_in =
            let submod_pairs =
                    -- submodule method inputs
                    [(veri_id, pprops) |
                         -- for each instance
                         v <- vs,
                         -- create the method name map
                         let nmap = M.fromList $
                                    createVerilogNameMapForAVInst flags v,
                         -- for each method (not clocks or resets)
                         vfi@(Method {}) <- vFields (avi_vmi v),
                         -- for each method input part (args and enables)
                         (methpart, (vname, pprops))
                             <- (zip (map MethodArg [1..]) (vf_inputs vfi)) ++
                                case (vf_enable vfi) of
                                    Nothing -> []
                                    Just port -> [(MethodEnable, port)],
                         -- for each port copy
                         ino <- if (vf_mult vfi > 1) then
                                  map Just [0 .. vf_mult vfi]
                                else [Nothing],
                         -- construct the method output signal name
                         let meth_id = mkMethId (avi_vname v)
                                                (vf_name vfi)
                                                ino
                                                methpart,
                         -- convert to Verilog signal name
                         let veri_id = xLateIdUsingFStringMap nmap meth_id
                    ] ++
                    -- submodule argument inputs
                    [(d, pprops) |
                         (AVInst { avi_vmi = vi, avi_iargs = es }) <- vs,
                         (a, e) <- zip (vArgs vi) es,
                         -- AState has converted Clock/Reset to Port
                         let pprops =
                                 case a of
                                   (Port (_,pps) _ _) -> pps
                                   (Param _) -> [VPconst] -- XXX?
                                   arg -> internalError
                                              ("VIOProps wireMap_in: " ++
                                               "unexpected arg: " ++
                                               ppReadable arg) ,
                         -- only carry these props to direct refs
                         let ds = aVars e,
                         all (\i -> okUse i e) ds,
                         d <- ds
                    ]
                -- inputs can also feed into outputs;
                -- we use [] for the properties of the output
                -- (since it is a use that we can conclude nothing about,
                --  not "unused")
                -- XXX this should be OK?
                output_pairs =
                    [ (o, []) | (o,_) <- os ]
            in
                M.fromList (submod_pairs ++ output_pairs)

        -- use a map to limit search over all definition
        -- key is AId data is list of defs where key is used.
        defuseMap :: M.Map AId (S.Set AId)
        defuseMap = getDefUses ds

        -- given a signal, this determines its props
        getSignalInProp :: AId -> [VeriPortProp]
        getSignalInProp i =
            let
                -- there are two sources of port props:
                --   * wireMap_in (submod inputs, top-mod outputs)
                --   * following defs (via defuseMap) to eventually
                --     reach Ids in wireMap_in
                -- For most of the Ids in the wireMap_in, there should be
                -- no uses in the defs to follow.  But some can be followed.
                -- So in order to support that (and reduce the requirements
                -- on defs in ASPackage), we check both sources and merge.

                wiremap_props =
                    case (M.lookup i wireMap_in) of
                        Just ps -> ps
                        Nothing -> [VPunused]

                defuse_props =
                    let user_set = M.findWithDefault (S.empty) i defuseMap
                    in -- is it unused?
                       if (S.null user_set)
                       then [VPunused]
                       else
                         -- determine if the uses are "direct"
                         -- (direct reference, concat, or extract, but no
                         -- other functions on the value)
                         let uses = [ if noUse i user_e
                                      then Just []
                                      else if okUse i user_e
                                           then Just [user]
                                           else Nothing
                                      | user <- S.toList user_set,
                                        let user_e = adef_expr $ getDef user ]
                         in
                             -- if any are not direct uses,
                             -- then we conclude nothing
                             if (any isNothing uses)
                             then []
                             else let users = concat $ catMaybes uses
                                      userprops = map getSignalInProp users
                                  in
                                      -- a prop is only valid if all uses
                                      -- have that prop
                                      joinInProps userprops
            in
                -- merge the props from the two sources
                joinInProps [wiremap_props, defuse_props]

        -- ----------
        -- construct the VeriPortProp list for an inout

        getIOProp :: AId -> [VeriPortProp]
        getIOProp i =
            -- if it's an interface Inout, then treat it like an output;
            -- otherwise, it's an argument Inout, so treat it like an input
            case M.lookup i ioDefMap of
              Just _  -> getOProp i
              Nothing -> getIProp i


-- This used to return (Map AId (Set ADef)), which meant that the whole def
-- had to be compared, when inserting new elements, which was inefficient
-- for large expressions.  Changed it to be just a set of the AId, which
-- requires that the def needs to be looked up.  If we're willing to trade
-- off memory, we could use (Map AId ADef) instead of (Set AId) to avoid
-- the lookup.  We could also consider memo-izing "getSignalInProp", if
-- recomputation becomes a problem.  But it's likely that the number of
-- defs being followed is small, so this seems like the right trade-off.
--
getDefUses :: [ADef] -> M.Map AId (S.Set AId)
getDefUses defs = foldl addDef M.empty defs
  where
    addDef :: M.Map AId (S.Set AId) -> ADef -> M.Map AId (S.Set AId)
    addDef m0 def@(ADef def_id _ def_e _) = foldl (addUses) m0 used
      where
        used = aVars def_e
        addUses :: M.Map AId (S.Set AId) -> AId -> M.Map AId (S.Set AId)
        addUses m use_id = M.insertWith S.union use_id (S.singleton def_id) m


okUse :: AId -> AExpr -> Bool
okUse i (APrim _ _ PrimConcat es)         = and (map (okUse i) es)
okUse i (APrim _ _ PrimExtract [e, _, _]) = okUse i e
okUse i (APrim _ _ _ es)                  = and (map (noUse i) es)
okUse i (ANoInlineFunCall _ _ _ es)       = and (map (noUse i) es)
okUse i (AFunCall _ _ _ _ es)             = and (map (noUse i) es)
okUse i (ASInt _ _ _)                     = True
okUse i (ASStr _ _ _)                     = True
okUse i (ASPort _ _)                      = True
okUse i (ASParam _ _)                     = True
okUse i (ASDef _ _)                       = True
okUse i (ASAny _ _)                       = True
okUse i e                                 = internalError ("getIOProps.okUse " ++ show (i,e))


noUse :: AId -> AExpr -> Bool
noUse i (APrim _ _ _ es)     = and (map (noUse i) es)
noUse i (ANoInlineFunCall _ _ _ es) = and (map (noUse i) es)
noUse i (AFunCall _ _ _ _ es) = and (map (noUse i) es)
noUse i (AMethCall _ _ _ es) = and (map (noUse i) es)
noUse i (ASPort _ i')        = i /= i'
noUse i (ASParam _ i')       = i /= i'
noUse i (ASDef _ i')         = i /= i'
noUse _ _                    = True

-- compute the size of a port
size :: AType -> Integer
size (ATBit n) = n
size (ATAbstract a _) | a == idPrimAction = 1
size (ATAbstract a [n]) | a == idInout_ = n
size (ATString _ ) = 0
size t = internalError ("getIOProps.size: " ++ show t)
