module PragmaCheck ( checkModuleArgPragmas,
                     checkModulePortNames,
                     ArgInfo(..),
                     extractVTPairs,
                     renamePProps
                   ) where

import qualified Data.Map as M

import Control.Monad(msum)
import Data.List(groupBy, sort, partition, nub, intersect)
import Data.Maybe(listToMaybe, mapMaybe, catMaybes, fromMaybe)

import Util(thd, fst3, headOrErr)

import Verilog(vKeywords, vIsValidIdent)

import Error(EMsg, ErrMsg(..))
import ErrorMonad(ErrorMonad(..))
import Position
import Id
import PreIds(idDefaultClock, idDefaultReset, idCLK, idCLK_GATE, mk_no)

import FStringCompat
import PreStrings(fsUnderscore)
import Flags(Flags(..))

import Pragma
import CType
import Type(tClock, tReset)


-- ==============================

data ArgInfo = Simple Id CType
             -- Bool tracks Vector vs. ListN
             | Vector Bool Id CType [ArgInfo]

extractVTPairs :: ArgInfo -> [(Id, CType)]
extractVTPairs (Vector _ _ _ ais) = concatMap extractVTPairs ais
extractVTPairs (Simple v t) = [(v,t)]


-- adjust PProps to account for Vector arguments
renamePProps :: [(Id, CType, ArgInfo)] -> [PProp] -> [PProp]
renamePProps vtis pps =
    let renameMap = M.fromList
                       [ (i_orig, new_is)
                             | (i_orig, _, ai@(Vector {})) <- vtis,
                               let new_is = map fst (extractVTPairs ai) ]
        fixPProp (PPclock_osc is) =
            (PPclock_osc (concatMap fixRenameProp is))
        fixPProp (PPclock_gate is) =
            (PPclock_gate (concatMap fixRenameProp is))
        fixPProp (PPreset_port is) =
            (PPreset_port (concatMap fixRenameProp is))
        fixPProp (PParg_param is) =
            (PParg_param (concatMap fixRenameProp is))
        fixPProp (PParg_port is) =
            (PParg_port (concatMap fixRenameProp is))
        fixPProp (PParg_clocked_by is) =
            (PParg_clocked_by (concatMap fixClkRstProp is))
        fixPProp (PParg_reset_by is) =
            (PParg_reset_by (concatMap fixClkRstProp is))
        fixPProp (PPgate_inhigh is) =
            (PPgate_inhigh (concatMap fixSetProp is))
        fixPProp (PPgate_unused is) =
            (PPgate_unused (concatMap fixSetProp is))
        fixPProp (PPparam is) =
            (PPparam (concatMap fixSetProp is))
        fixPProp (PPgate_input_clocks is) =
            (PPgate_input_clocks (concatMap fixSetProp is))
        fixPProp p = p

        fixSetProp :: Id -> [Id]
        fixSetProp i1 = fromMaybe [i1] (M.lookup i1 renameMap)

        fixClkRstProp :: (Id, String) -> [(Id, String)]
        fixClkRstProp (i1,s) =
            case (M.lookup i1 renameMap) of
              Just new_is -> [ (new_i,s) | new_i <- new_is ]
              Nothing -> [(i1,s)]

        fixRenameProp :: (Id, String) -> [(Id, String)]
        fixRenameProp (i1,s) =
            let istr = getIdBaseString i1
                rename i2 str = let i2str = getIdBaseString i2
                                    suf = drop (length istr) i2str
                                in  str ++ suf
            in  case (M.lookup i1 renameMap) of
                  Just new_is -> [ (new_i,rename new_i s) | new_i <- new_is ]
                  Nothing -> [(i1,s)]
    in
        map fixPProp pps


-- ==============================
-- Initial sanity check of module pragmas relating to module arguments

modifies :: Id -> PProp -> Bool
modifies n (PPclock_osc ps)   = n `elem` (map fst ps)
modifies n (PPclock_gate ps)  = n `elem` (map fst ps)
modifies n (PPreset_port ps)  = n `elem` (map fst ps)
modifies n (PParg_param ps)   = n `elem` (map fst ps)
modifies n (PParg_port ps)    = n `elem` (map fst ps)
modifies n (PParg_clocked_by ps)
                              = n `elem` (map fst ps)
modifies n (PParg_reset_by ps)
                              = n `elem` (map fst ps)
modifies n (PPgate_inhigh is) = n `elem` is
modifies n (PPgate_unused is) = n `elem` is
modifies n (PPparam is)       = n `elem` is
modifies _ _                  = False

isParam :: PProp -> Bool
isParam (PPparam _)     = True
isParam (PParg_param _) = True
isParam _               = False

isOscOrGate :: PProp -> Bool
isOscOrGate (PPclock_osc _)   = True
isOscOrGate (PPclock_gate _)  = True
isOscOrGate (PPgate_inhigh _) = True
isOscOrGate (PPgate_unused _) = True
isOscOrGate _                 = False

isReset :: PProp -> Bool
isReset (PPreset_port _)     = True
isReset (PParg_clocked_by _) = True
isReset _                    = False

isArg :: PProp -> Bool
isArg (PParg_port _)       = True
isArg (PParg_clocked_by _) = True
isArg (PParg_reset_by _)   = True
isArg _                    = False

checkArgType :: (PProp -> Bool) -> String -> (Id, [PProp]) -> Maybe EMsg
checkArgType ok reason (arg, ps) =
  let bad = filter (not . ok) ps
  in  case bad of
        []     -> Nothing
        (pp:_) -> Just (getPosition arg,
                        EAttributeOnWrongArgType (getModulePragmaName pp)
                                                 (getIdBaseString arg)
                                                 reason)

checkArgName :: [String] -> Position -> PProp -> Maybe EMsg
checkArgName arg_names pos pp =
  let ns = getPragmaArgNames (sanitize pp)
  in listToMaybe [ (pos, EAttributeNoSuchArg (getModulePragmaName pp) n)
                 | n <- ns
                 , n `notElem` arg_names ]
  where ignored  = [ idDefaultClock, idDefaultReset ]
        ignored2 = zip ignored (repeat "")
        fixed xs ign = [ x | x <- xs, x `notElem` ign ]
        sanitize (PPclock_osc ps)   = PPclock_osc   (fixed ps ignored2)
        sanitize (PPreset_port ps)  = PPreset_port  (fixed ps ignored2)
        sanitize (PPgate_inhigh is) = PPgate_inhigh (fixed is ignored)
        sanitize (PPgate_unused is) = PPgate_unused (fixed is ignored)
        sanitize pp                 = pp

checkArgClockedBy :: [String] -> (Id, [PProp]) -> Maybe EMsg
checkArgClockedBy clk_names (arg, ps) =
    let mclk = listToMaybe $ catMaybes $
                 [ lookup arg xs | PParg_clocked_by xs <- ps ]
    in  case mclk of
          Just str | (str `notElem` clk_names)
            -> let arg_pos = getPosition arg
               in  Just (arg_pos, EClockedByBadName str clk_names)
          _ -> Nothing

checkArgResetBy :: [String] -> (Id, [PProp]) -> Maybe EMsg
checkArgResetBy rst_names (arg, ps) =
    let mrst = listToMaybe $ catMaybes $
                 [ lookup arg xs | PParg_reset_by xs <- ps ]
    in  case mrst of
          Just str | (str `notElem` rst_names)
            -> let arg_pos = getPosition arg
               in  Just (arg_pos, EResetByBadName str rst_names)
          _ -> Nothing


-- This is the entry point for sanity checking module argument pragmas
-- (even when not synthesizing the module, these checks can be made)
checkModuleArgPragmas :: Position -> [PProp] -> [PProp] ->
                         [(Id, CType, ArgInfo)] ->
                         ErrorMonad ()
checkModuleArgPragmas pos pps_orig pps vtis =
    let

    -- ---------------
    -- compute pragma info for each port

        -- ----------
        -- implicit clock and reset arguments

        default_clk_arg =
            if (hasDefaultClk pps)
            then let id = setIdPosition pos idDefaultClock
                     ty = tClock
                 in  [(id, ty, Simple id ty)]
            else []
        default_rst_arg =
            if (hasDefaultRst pps)
            then let id = setIdPosition pos idDefaultReset
                     ty = tReset
                 in  [(id, ty, Simple id ty)]
            else []

        -- ----------
        -- Functions to identify the type of arguments

        isVector (Vector {}) = True
        isVector (Simple {}) = False

        isCoreTypeOf t (Simple i it) = (it == t)
        isCoreTypeOf t (Vector _ _ it []) = (it == t)
        isCoreTypeOf t (Vector _ _ it is) =
            (it == t) || isCoreTypeOf t (headOrErr "isCoreTypeOf" is)

        -- we could check "t", but "i" also contains the type
        isClk (_,t,i) = isCoreTypeOf tClock i
        isRst (_,t,i) = isCoreTypeOf tReset i

        -- save effort by looking in the pre-expanded PProps
        isParamArg (i,_,_) = isParamModArg pps_orig i

        -- ----------
        -- Separate the arguments by type

        (cs,others)   = partition isClk vtis
        (rs,others')  = partition isRst others
        (params,ports) = partition isParamArg others'
        clks  = default_clk_arg ++ cs
        rsts  = default_rst_arg ++ rs

        -- expand the arg names (for Vector) and pair the arg names
        -- with the PProp which modify them (using the PProps which
        -- have themselves been expanded)
        clk_info =
            [ (i, ps) | (i, _, Simple {}) <- clks,
                        let ps = filter (modifies i) pps ] ++
            [ (i, ps) | (_, _, Vector _ _ _ ais) <- clks,
                        (i,_) <- concatMap extractVTPairs ais,
                        let ps = filter (modifies i) pps ]
        rst_info =
            [ (i, ps) | (i, _, Simple {}) <- rsts,
                        let ps = filter (modifies i) pps ] ++
            [ (i, ps) | (_, _, Vector _ _ _ ais) <- rsts,
                        (i,_) <- concatMap extractVTPairs ais,
                        let ps = filter (modifies i) pps ]
        port_info =
            [ (i, ps) | (i, _, Simple {}) <- ports,
                        let ps = filter (modifies i) pps ] ++
            [ (i, ps) | (_, _, Vector _ _ _ ais) <- ports,
                        (i,_) <- concatMap extractVTPairs ais,
                        let ps = filter (modifies i) pps ]
        param_info =
            [ (i, ps) | (i, _, Simple {}) <- params,
                        let ps = filter (modifies i) pps ] ++
            [ (i, ps) | (_, _, Vector _ _ _ ais) <- params,
                        (i,_) <- concatMap extractVTPairs ais,
                        let ps = filter (modifies i) pps ]

        all_info = clk_info ++ rst_info ++ port_info ++ param_info

    -- ---------------
    -- it is an error if there is an empty clock/reset prefix and no name
    -- given for a default clock/reset

        emsg0 =
            let clk_prefixes = [s | PPCLK s <- pps ]
                clk_prefix = listToMaybe clk_prefixes
                ps = filter (modifies idDefaultClock) pps
                default_clock_osc =
                    listToMaybe $ catMaybes $
                      [ lookup idDefaultClock xs | PPclock_osc xs <- ps ]
            in  case (clk_prefixes, clk_prefix, default_clock_osc) of
                    (s:_: _, _, _) ->
                        Just (pos, EMultipleAttribute $ getModulePragmaName $ PPCLK s)
                    (_, Just "", Nothing) ->
                        Just (pos, EEmptyPrefixNoPortName
                                       (getIdBaseString idDefaultClock))
                    _ -> Nothing

        emsg1 =
            let gate_prefixes = [ s | PPGATE s <- pps ]
                gate_prefix = listToMaybe gate_prefixes
                ps = filter (modifies idDefaultClock) pps
                default_clock_gate =
                    listToMaybe $ catMaybes $
                      [ lookup idDefaultClock xs | PPclock_gate xs <- ps ]
            in  case (gate_prefixes, gate_prefix, default_clock_gate) of
                    (s:_:_, _, _) ->
                        Just (pos, EMultipleAttribute $ getModulePragmaName $ PPGATE s)
                    (_, Just "", Nothing) ->
                        Just (pos, EEmptyPrefixNoPortName
                                       (getIdBaseString idDefaultClock))
                    _ -> Nothing

        emsg2 =
            let rst_prefixes = [ s | PPRSTN s <- pps ]
                rst_prefix = listToMaybe rst_prefixes
                ps = filter (modifies idDefaultReset) pps
                default_reset_port =
                    listToMaybe $ catMaybes $
                      [ lookup idDefaultReset xs | PPreset_port xs <- ps ]
            in  case (rst_prefixes, rst_prefix, default_reset_port) of
                    (s:_:_, _, _) -> Just (pos, EMultipleAttribute $ getModulePragmaName $ PPRSTN s)
                    (_, Just "", Nothing) ->
                        Just (pos, EEmptyPrefixNoPortName
                                       (getIdBaseString idDefaultReset))
                    _ -> Nothing

    -- ---------------
    -- it is an error if a clock is listed as both gated and ungated

        gated_clks = concat [ is | PPgate_input_clocks is <- pps ]
        ungated_clks = nub $ concat ([ is | PPgate_inhigh is <- pps ] ++
                                     [ is | PPgate_unused is <- pps ])
        conflicted_clks = gated_clks `intersect` ungated_clks
        emsg3 = case conflicted_clks of
                  (i:_) -> Just (getPosition i,
                                 EConflictingGateAttr (getIdBaseString i))
                  []    -> Nothing

    -- ---------------
    -- it is an error to apply an attribute to a param or to an
    -- argument of the wrong type

        emsg4 = msum $ concat $
                [ map (checkArgType isOscOrGate "a Clock")     clk_info
                , map (checkArgType isReset "a Reset")         rst_info
                , map (checkArgType isArg   "a port argument") port_info
                , map (checkArgType isParam "a parameter, not a module port")
                      param_info
                ]

    -- ---------------
    -- it is an error to apply an attribute to a non-existent argument

        all_args = [ getIdBaseString i | (i,_) <- all_info ]
        emsg5    = msum $ map (checkArgName all_args pos) pps

    -- ---------------
    -- it is an error if the associated clock is not one of the input clks

        -- XXX don't allow reference to vector clocks yet
        clks_nonvec = filter (not . isVector . thd) clks
        clk_names = ["no_clock"] ++ map (getIdBaseString . fst3) clks_nonvec
        emsg6     = msum $ map (checkArgClockedBy clk_names)
                               -- only need to check resets and ports
                               (rst_info ++ port_info)

    -- ---------------
    -- it is an error if the associated reset is not one of the input rsts

        -- XXX don't allow reference to vector resets yet
        rsts_nonvec = filter (not . isVector . thd) rsts
        rst_names = ["no_reset"] ++ map (getIdBaseString . fst3) rsts_nonvec
        emsg7    = msum $ map (checkArgResetBy rst_names)
                               -- only need to check ports
                               port_info

    -- ---------------
    -- report any errors or warnings

    in  case (msum [ emsg0, emsg1, emsg2, emsg3
                   , emsg4, emsg5, emsg6, emsg7 ]) of
          (Just e) -> EMError [e]
          Nothing  -> EMResult ()


-- ==============================
-- Check port names (for clash, keyword clash, non-verilog Id)

data ArgPortInfo =
    API { api_arg        :: Id           -- arg name
        , api_type       :: CType        -- arg type
        -- whether the arg is a Vector element
        -- and the original name of the argument
        , api_vector     :: Maybe Id
        , api_prefix     :: Maybe String -- user-given prefix
        , api_given_name :: Maybe String -- user-given name
        , api_port       :: Maybe Id     -- port Id, if exists
        }
  deriving (Show)

-- get the name as the user knows it; for Vectors, this is different
-- than "pi_arg"
getAPIArgName :: ArgPortInfo -> Id
getAPIArgName (API { api_vector = Just i }) = i
getAPIArgName (API { api_arg = i }) = i


mkPortName :: Id -> Maybe String -> Maybe String -> Id -> Id
mkPortName _ _ (Just n) i = setIdBaseString i n
mkPortName _ (Just pfx) Nothing i
  | pfx == ""    = i
  | i == emptyId = setIdBaseString i pfx
  | otherwise    = mkIdPre (concatFString [(mkFString pfx), fsUnderscore]) i
mkPortName def_pfx Nothing Nothing i
  | def_pfx == emptyId = i
  | i == emptyId       = setIdBase i (getIdBase def_pfx)
  | otherwise = mkIdPre (concatFString [(getIdBase def_pfx), fsUnderscore]) i


-- This is the entry point for checking module port names (both arguments
-- and interface ports).  This is
checkModulePortNames :: Flags -> Position -> [PProp] ->
                        -- argument info
                        [(Id, CType, ArgInfo)] ->
                        -- interface info
                        [(Id, CType, [IfcPragma])] ->
                        -- return the mapping from argument port to type
                        ErrorMonad [(Id, CType)]
checkModulePortNames flgs pos pps vtis ftps =
    let
        idrstn = (mk_no . mkFString . resetName) flgs

    -- ---------------
    -- Get the prefixes

        osc_prefix  = listToMaybe [ s | PPCLK s <- pps ]
        gate_prefix = listToMaybe [ s | PPGATE s <- pps ]
        rst_prefix  = listToMaybe [ s | PPRSTN s <- pps ]

    -- ---------------
    -- compute naming info for each module argument

        -- ----------
        -- implicit clock and reset arguments

        default_clk_arg =
            if (hasDefaultClk pps)
            then let id = setIdPosition pos idDefaultClock
                     ty = tClock
                 in  [(id, ty, Simple id ty)]
            else []
        default_rst_arg =
            if (hasDefaultRst pps)
            then let id = setIdPosition pos idDefaultReset
                     ty = tReset
                 in  [(id, ty, Simple id ty)]
            else []

        -- ----------
        -- Functions to identify the type of arguments

        isCoreTypeOf t (Simple i it) = (it == t)
        isCoreTypeOf t (Vector _ _ it []) = (it == t)
        isCoreTypeOf t (Vector _ _ it is) =
            (it == t) || isCoreTypeOf t (headOrErr "isCoreTypeOf" is)

        -- we could check "t", but "i" also contains the type
        isClk (_,t,i) = isCoreTypeOf tClock i
        isRst (_,t,i) = isCoreTypeOf tReset i

        -- ----------
        -- Separate the arguments by type

        (cs,others)   = partition isClk vtis
        (rs,others')  = partition isRst others
        (params,ports) = partition (\(i,_,_) -> isParamModArg pps i) others'
        clks  = default_clk_arg ++ cs
        gates = filter (\(i,_,_) -> isGatedInputClk pps i) clks
        rsts  = default_rst_arg ++ rs

        clk_arg_oscs =
            let mkOscPort (i,t,mv) =
                    let ps = filter (modifies i) pps
                        name = listToMaybe $ catMaybes $
                                 [ lookup i xs | PPclock_osc xs <- ps ]
                        -- default clock base name is ""
                        i' = if (i == idDefaultClock)
                             then setIdBaseString i ""
                             else i
                        port = Just (mkPortName idCLK osc_prefix name i')
                    in  (API i t mv osc_prefix name port)
            in  [ mkOscPort (i,t,Nothing)
                  | (i,t,Simple {}) <- clks ] ++
                [ mkOscPort (i,t,Just i_orig)
                  | (i_orig,_,Vector _ _ _ ais) <- clks,
                    (i,t) <- concatMap extractVTPairs ais ]

        clk_arg_gates =
            let mkGatePort (i,t,mv) =
                    let ps = filter (modifies i) pps
                        n0 = catMaybes $
                               [ lookup i xs | PPclock_gate xs <- ps ]
                        n1 = [ "" | PPgate_inhigh is <- ps, i `elem` is ]
                        n2 = [ "" | PPgate_unused is <- ps, i `elem` is ]
                        name = listToMaybe (n2 ++ n1 ++ n0)
                        -- default clock base name is ""
                        i' = if (i == idDefaultClock)
                             then setIdBaseString i ""
                             else i
                        port = if (null n1 && null n2)
                               then Just (mkPortName idCLK_GATE gate_prefix name i')
                               else Nothing
                    in  (API i t mv gate_prefix name port)
            in  [ mkGatePort (i,t,Nothing)
                  | (i,t,Simple {}) <- gates ] ++
                [ mkGatePort (i,t,Just i_orig)
                  | (i_orig,_,Vector _ _ _ ais) <- gates,
                    (i,t) <- concatMap extractVTPairs ais ]

        rst_arg_ports =
            let mkRstPort (i,t,mv) =
                    let ps = filter (modifies i) pps
                        name = listToMaybe $ catMaybes $
                                 [ lookup i xs | PPreset_port xs <- ps ]
                        -- default reset base name is ""
                        i' = if (i == idDefaultReset)
                             then setIdBaseString i ""
                             else i
                        port = Just (mkPortName idrstn rst_prefix name i')
                    in  (API i t mv rst_prefix name port)
            in  [ mkRstPort (i,t,Nothing)
                  | (i,t,Simple {}) <- rsts ] ++
                [ mkRstPort (i,t,Just i_orig)
                  | (i_orig,_,Vector _ _ _ ais) <- rsts,
                    (i,t) <- concatMap extractVTPairs ais ]

        port_arg_ports =
            let mkPort (i,t,mv) =
                    let ps = filter (modifies i) pps
                        name = listToMaybe $ catMaybes $
                                 [ lookup i xs | PParg_port xs <- ps ]
                        port = Just (mkPortName emptyId Nothing name i)
                    in  (API i t mv Nothing name port)
            in  [ mkPort (i,t,Nothing)
                  | (i,t,Simple {}) <- ports ] ++
                [ mkPort (i,t,Just i_orig)
                  | (i_orig,_,Vector _ _ _ ais) <- ports,
                    (i,t) <- concatMap extractVTPairs ais ]

        param_arg_params =
            let mkParam (i,t,mv) =
                    let ps = filter (modifies i) pps
                        name = listToMaybe $ catMaybes $
                                 [ lookup i xs | PParg_param xs <- ps ]
                        param = Just (mkPortName emptyId Nothing name i)
                    in  (API i t mv Nothing name param)
            in  [ mkParam (i,t,Nothing)
                  | (i,t,Simple {}) <- params ] ++
                [ mkParam (i,t,Just i_orig)
                  | (i_orig,_,Vector _ _ _ ais) <- params,
                    (i,t) <- concatMap extractVTPairs ais ]

        all_arg_info = clk_arg_oscs ++ clk_arg_gates ++ rst_arg_ports ++
                       port_arg_ports ++ param_arg_params

    -- ---------------
    -- compute naming info for each the provided interface fields

        isClkField (_,t,_) = t == tClock
        isRstField (_,t,_) = t == tReset
    
        (clk_fs, other_fs) = partition isClkField ftps
        (rst_fs, _) = partition isRstField other_fs

    -- ---------------
    -- check that no arg port name clashes with another port name and
    -- check that no arg port name clashes with a Verilog keyword and
    -- check that each arg port name is a valid Verilog identifier

    -- We also check that param arguments do not clash, but note that
    -- XXX parameters will be referred to as "ports" in the error message

        arg_names = sort [ (getIdBaseString n, getAPIArgName api)
                         | api@(API { api_port = Just n }) <- all_arg_info ]
        arg_same_name = filter (\xs -> (length xs) > 1) $
                               groupBy (\(n1,_) (n2,_) -> n1 == n2) arg_names
        arg_kw_clash  = filter (\(n,_) -> n `elem` vKeywords) arg_names
        arg_bad_ident = filter (\(n,_) -> not (vIsValidIdent n)) arg_names
        emsgs0 = let mkErr xs =
                         let ns = [(n, getPosition i, getIdBaseString i)
                                       | (n,i) <- xs ]
                         in  (pos, EPortsSameName ns)
                 in  map mkErr arg_same_name
        emsgs1 = let mkErr (n,i) = (getPosition i, EPortKeywordClash n)
                 in  map mkErr arg_kw_clash
        emsgs2 = let mkErr (n,i) = (getPosition i, EPortNotValidIdent n)
                 in  map mkErr arg_bad_ident

    -- ---------------
    -- warn if a prefix is supplied but never used

        prefixes = [ osc_prefix, gate_prefix, rst_prefix ]
        uses_prefix (API _ _ _ (Just _) Nothing _) = True
        uses_prefix _                              = False
        osc_prefix_used = (any uses_prefix clk_arg_oscs) ||
                          -- output clocks use the prefix
                          (not (null clk_fs))
        gate_prefix_used = (any uses_prefix clk_arg_gates) ||
                           -- output clocks always have a gate (for now)
                          (not (null clk_fs))
        reset_prefix_used = (any uses_prefix rst_arg_ports) ||
                            -- output resets use the prefix
                            (not (null rst_fs))
        prefix_used = [ osc_prefix_used, gate_prefix_used, reset_prefix_used ]
        pfx_tuples = zip3 ["clock", "gate", "reset"] prefixes prefix_used
        wmsgs0 = [ (pos, WUnusedPrefix k pfx)
                 | (k,(Just pfx),False) <- pfx_tuples
                 ]

    -- ---------------
    -- warn if gate_all_clocks is overridden on every clock

        -- output clocks are always gated (for now), so they are not
        -- included in this check

        all_gated = any null [ is | PPgate_input_clocks is <- pps ]
        no_ports  = null (mapMaybe api_port clk_arg_gates)
        wmsgs1    = if (all_gated && no_ports)
                    then [(pos, WGateAllClocksIgnored)]
                    else []

    -- ---------------
    -- compute the result:
    -- a mapping from module argument port names to the types

        -- for now, just args and inouts (no clock, reset, or param)
        porttypes = [ (n,t) |( API { api_port = Just n,
                                     api_type = t }) <- port_arg_ports ]
        result = porttypes

    -- ---------------
    -- report any errors or warnings

        -- report all errors, since none trump any others
        emsgs = emsgs0 ++ emsgs1 ++ emsgs2

        wmsgs = wmsgs0 ++ wmsgs1

    in  if (null emsgs)
        then if (null wmsgs)
             then EMResult result
             else EMWarning wmsgs result
        else EMError emsgs


-- ==============================
