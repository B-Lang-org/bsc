module SystemCWrapper (checkSystemCIfc, wrapSystemC) where

import Flags(Flags(..), verbose)
import Error(internalError, ErrMsg(..), ErrorHandle, bsError)
import Position(noPosition)
import Id(getIdBaseString, getIdString, isRdyId, dropReadyPrefixId)
import Pragma(isAlwaysRdy, isEnWhenRdy)
import FileNameUtil(mkCxxName, mkHName)
import ASyntax(AAbstractInput(..), AIFace(..),
               AExpr(..), AClock(..),
               aIfaceArgs, aif_name, aIfaceProps)
import ASyntaxUtil
import VModInfo(vName_to_id, VPathInfo(..))
import Wires
import AScheduleInfo(AScheduleInfo(..))
import SchedInfo(SchedInfo(..))
import SimPackage(SimSystem(..), SimPackage(..), findPkg, getPortInfo)
import SimCCBlock(pfxPort, pfxMeth, pfxMod)
import CCSyntax
import TopUtils(putStrLnF)
import Control.Monad(when)
import Data.Maybe(maybeToList, mapMaybe)
import PPrint
import Data.List(intersperse, partition)
import qualified Data.Map as M

--import Debug.Trace

checkSystemCIfc :: ErrorHandle -> Flags -> SimSystem -> IO ()
checkSystemCIfc errh flags sim_system = do
    let top_pkg = findPkg (ssys_packages sim_system) (ssys_top sim_system)
        pps = sp_pps top_pkg
    let pathinfo@(VPathInfo paths) = sp_pathinfo top_pkg
        path_desc = ppReadable pathinfo
        path_err = (noPosition,ESystemCWrapperComboPaths path_desc)
    when (not (null paths)) $ bsError errh [path_err]
    let isBad m@(AIDef {})         = not (null (aIfaceArgs m))
        isBad m@(AIActionValue {}) = -- we allow ActionValue methods only
                                     -- if they have no arguments and no enable
                                     not ((null (aIfaceArgs m)) &&
                                          (isEnWhenRdy pps (aif_name m)))
        isBad _                    = False
        bad_methods = [ getIdBaseString (aif_name m)
                      | m <- sp_interface top_pkg
                      , isBad m
                      ]
        method_err = (noPosition,ESystemCWrapperInvalidMethods bad_methods)
    when (not (null bad_methods)) $ bsError errh [method_err]
    let is_value_method m d@(AIDef {})         = (aif_name d) == m
        is_value_method m d@(AIActionValue {}) = (aif_name d) == m
        is_value_method _ _                    = False
        rbms = [ (m,rb)
               | (m,rb) <- rulesBeforeMethods (asi_v_sched_info (sp_schedule top_pkg))
               , any (is_value_method m) (sp_interface top_pkg)
               ]
        describe (m,rs) =
          let mname = pPrint PDReadable 0 m
              rnames = [ pPrint PDReadable 0 r | (Left r) <- rs ]
              vmnames = [ pPrint PDReadable 0 vm | (Right vm) <- rs ]
              rdoc = (text "schedules after the rule(s):") <+> (hsep rnames)
              mdoc = (text "schedules after rules via the method call(s):") <+> (hsep vmnames)
          in case (rnames,vmnames) of
               ([],[]) -> internalError "checkSystemCIfc: no rules or methods"
               (_,[])  -> (mname, rdoc)
               ([],_)  -> (mname, mdoc)
               (_,_)   -> (mname, rdoc <+> (text "and") <+> mdoc)
        rbms_desc = map describe rbms
        rbm_err = (noPosition,ESystemCWrapperRuleBeforeMethod rbms_desc)
    when (not (null rbms)) $ bsError errh [rbm_err]

wrapSystemC:: Flags -> SimSystem -> IO [(String,String)]
wrapSystemC flags sim_system = do
    when (verbose flags) $ putStrLnF "generating SystemC file"
    let top_pkg  = findPkg (ssys_packages sim_system) (ssys_top sim_system)
        pps      = sp_pps top_pkg
        name     = getIdBaseString (sp_name top_pkg)
        h_name   = mkHName Nothing "" (name ++ "_systemc")
        cxx_name = mkCxxName Nothing "" (name ++ "_systemc")
        h_includes   = [ cpp_include "bluesim_kernel_api.h"
                       , cpp_include (mkHName Nothing "" name)
                       , cpp_include ("model_" ++ name ++ ".h")
                       ]
        cxx_includes = [ cpp_include "bluesim_systemc.h"
                       , cpp_include h_name
                       ]
        class_name   = "SC_MODULE(" ++ name ++ ")"

        -- utility fns
        obj_ref o m = (var o) `cArrow` m
        obj_call o m args = (obj_ref o m) `cCall` args
        cvt_wide n x =
            let sc_type = if (n == 1)
                          then boolType
                          else classType "sc_bv" `templatedT` [ numType n ]
                conv = (var "bs_convert_wide_to_sysc") `templated` [sc_type]
            in if (n > 64)
               then conv `cCall` [x]
               else x
        read_port i = obj_call (getIdBaseString i) "read" []
        write_port (_,i,n,True) =
            let nm = getIdBaseString i
                arg = cvt_wide n $ obj_ref "_model_inst" (pfxPort ++ nm)
            in obj_call nm "write" [ arg ]
        write_port (mid,i,n,False) =
            let nm = getIdBaseString i
                meth = pfxMeth ++ (getIdBaseString mid)
                arg = cvt_wide n $ obj_call "_model_inst" meth []
            in obj_call nm "write" [ arg ]
        sample_port (n,i) =
            let nm = getIdBaseString i
                sc_type = if (n == 1)
                          then boolType
                          else classType "sc_bv" `templatedT` [ numType n ]
                bs_type = bitsType n CTunsigned
                conv = (var "bs_convert_from_sysc") `templated` [sc_type, bs_type]
                rhs = conv `cCall` [ read_port i ]
            in stmt (obj_ref "_model_inst" (pfxPort ++ nm)) `assign` rhs

        -- clk and reset ports
        clk_inputs    = concat [ (osc:(maybeToList mgate))
                               | (AAI_Clock osc mgate) <- sp_inputs top_pkg
                               ]
        rst_inputs    = [ rst | (AAI_Reset rst) <- sp_inputs top_pkg ]
        bool_in_port_type = classType "sc_in" `templatedT` [classType "bool"]
        clk_rst_decls = [ decl $ (mkVar (getIdBaseString i)) `ofType` bool_in_port_type
                        | i <- (clk_inputs ++ rst_inputs)
                        ]

        -- module ports
        method_info = mapMaybe (getPortInfo pps) (sp_interface top_pkg)
        mk_port_map_entry (mid, (en, ins, ri, act, _)) =
            let en_list  = maybe [] (\vn -> [(1,vName_to_id vn,True,False)]) en
                in_list  = [ (aSize t,i,True,False) | (t,i,_) <- ins ]
                ret_list = map (\(t,vn) -> (aSize t,vName_to_id vn,False,act)) ri
                ports = filter (\(n,_,_,_) -> n>0)
                               (en_list ++ in_list ++ ret_list)
                always_rdy = (isRdyId mid) && (isAlwaysRdy pps mid)
            in if ((null ports) || always_rdy) then Nothing else Just (mid, ports)
        port_entries = mapMaybe mk_port_map_entry method_info
        port_map = M.fromList port_entries
        merged_port_map =
          let (rs,nrs) = partition (isRdyId . fst) port_entries
              non_rdy_map = M.fromList nrs
              rdy_map     = M.fromList [ (dropReadyPrefixId mid, ps) | (mid,ps) <- rs ]
          in M.unionWith (++) non_rdy_map rdy_map
        mk_port_decl (n,i,is_input,_) =
            let t = if (n == 1)
                    then boolType
                    else classType "sc_bv" `templatedT` [numType n]
                pt = if is_input
                     then classType "sc_in" `templatedT` [t]
                     else classType "sc_out" `templatedT` [t]
            in  decl $ (mkVar (getIdBaseString i)) `ofType` pt
        port_decls  = concat [ [comment ((getIdBaseString m) ++ " method ports") (blankLines 0)] ++
                               (map mk_port_decl ps)
                             | (m,ps) <- M.toList merged_port_map
                             ]

        -- utility functions for grouping methods by domain
        meth_domains = M.fromList [ (aif_name aif, dom)
                                  | aif <- (sp_interface top_pkg)
                                  , let wp = aIfaceProps aif
                                  , let dom = wpClockDomain wp
                                  ]
        clock_domains = [ (getIdString (ae_objid (aclock_osc clk)), dom)
                        | (dom, clks) <- sp_clock_domains top_pkg
                        , clk <- clks
                        ]
        same_dom clk mid =
            case (lookup clk clock_domains) of
              Nothing   -> internalError $ "SystemCWrapper: unknown clock " ++ clk
              (Just cd) -> case (M.lookup mid meth_domains) of
                             Nothing -> internalError $ "SystemCWrapper: unknown method " ++ (getIdString mid)
                             (Just Nothing) -> internalError $ "SystemCWrapper: no clock domain for method " ++ (getIdString mid)
                             (Just (Just cd2)) -> (cd == cd2) || ((cd2 == noClockDomain) && (cd == initClockDomain))

        -- bluesim model instance
        sub_mod_type = classType (pfxMod ++ name)
        sub_mod      = decl $ ptr $ (mkVar "_model_inst") `ofType` sub_mod_type

        -- bluesim model handle
        model_hdl = decl $ (userType "tModel") (mkVar "_model_hdl")

        -- bluesim kernel state handle
        sim_hdl = decl $ (userType "tSimStateHdl") (mkVar "_sim_hdl")

        -- constructor & destructor
        -- XXX: this is an ugly hack to deal with the macro
        ctor_hack   = ctor (mkVar "SC_CTOR") [mkVar name]
        mk_init i   = let nm = getIdBaseString i
                      in (var nm) `cCall` [mkStr nm]
        meth_ports  = [ i | ports <- M.elems merged_port_map, (_,i,_,_) <- ports ]
        ilist       = map mk_init (clk_inputs ++ rst_inputs ++ meth_ports) ++
                      [ (var "_model_inst") `cCall` [mkNULL]
                      , (var "_model_hdl") `cCall` [mkNULL]
                      , (var "_sim_hdl") `cCall` [mkNULL]
                      ]
        setup_handler do_init i =
            let nm = getIdBaseString i
                change = (var nm) `cDot` "value_changed" `cCall` []
            in  [ blankLines 1
                , stmt $ (var "SC_METHOD") `cCall` [var ("handle_" ++ nm)]
                , stmt $ (var "sensitive") `cLShift` change
                ] ++
                ( if do_init
                  then []
                  else [ stmt $ (var "dont_initialize") `cCall` [] ]
                )
        ctor_stmts  = (concatMap (setup_handler False) clk_inputs) ++
                      (concatMap (setup_handler True)  rst_inputs)
        constructor = (define ctor_hack (block ctor_stmts)) `withInits` ilist
        dtor_stmts  = []
        destructor  = define (dtor (mkVar name)) (block dtor_stmts)

        -- simulation callbacks
        start_of_sim_stmts =
            [ (mkVar "_model_hdl") `assign`
                  ((var ("new_MODEL_" ++ name)) `cCall` [])
            , (mkVar "_sim_hdl") `assign`
                  ((var "bk_init") `cCall` [ var "_model_hdl", mkBool False])
            , stmt $ (var "bk_set_interactive") `cCall` [var "_sim_hdl"]
            , (mkVar "_model_inst") `assign`
                  (cCast (ptrType sub_mod_type)
                   ((var "bk_get_model_instance") `cCall` [var "_sim_hdl"]))
            ]
        sos_type = function void (mkVar "start_of_simulation") []
        start_of_sim_fn = virtual $ define sos_type (block start_of_sim_stmts)
        end_of_sim_stmts = [ stmt $ (var "bk_shutdown") `cCall` [var "_sim_hdl"] ]
        eos_type = function void (mkVar "end_of_simulation") []
        end_of_sim_fn = virtual $ define eos_type (block end_of_sim_stmts)

        -- clock and reset functions
        handler_type pfx i  =
            let nm = getIdBaseString i
                pfx' = if (pfx == "") then "" else (pfx ++ "::")
            in function void (mkVar (pfx' ++ "handle_" ++ nm)) []
        clk_stmts i =
            let nm = getIdBaseString i
                ins = [ (n,id)
                      | (mid,ports) <- M.toList port_map
                      , same_dom nm mid
                      , (n,id,True,_) <- ports
                      ]
                outs = [ (mid,id,n,act)
                       | (mid,ports) <- M.toList port_map
                       , same_dom nm mid
                       , (n,id,False,act) <- ports
                       ]
                get_clk = [ static . decl . (userType "tClock") $ (mkVar "_clk_hdl") `assign`
                            ((var "bk_get_clock_by_name") `cCall` [var "_sim_hdl", mkStr nm]) ]
                next_edge = ((var "bk_clock_edge_count") `cCall` [var "_sim_hdl", var "_clk_hdl", var "dir"]) `cAdd` (mkUInt64 1)
                sample_inputs =
                    [ comment "sample method input ports" (blankLines 0) ] ++
                    (map sample_port ins)
                do_vcd =
                    [ comment "update VCD waveforms for ports" (blankLines 0)
                    , decl . (userType "tTime") $ (mkVar "now") `assign`
                      ((((var "sc_time_stamp") `cCall` []) `cDot` "value") `cCall` [])
                    , stmt $ (var "bk_VCD_combo_update") `cCall` [var "_sim_hdl", var "now"]
                    ]
                stop_cond =
                    cOr ((var "bk_stopped") `cCall` [ var "_sim_hdl" ]) $
                    cOr ((var "bk_finished") `cCall` [ var "_sim_hdl" ]) $
                        ((var "bk_aborted") `cCall` [ var "_sim_hdl" ])
                exec =
                    [ comment "execute schedule" (blankLines 0)
                    , decl . (userType "tEdgeDirection") $ (mkVar "dir") `assign`
                      (cTernary (read_port i) (var "POSEDGE") (var "NEGEDGE"))
                    , stmt $ (var "bk_quit_after_edge") `cCall`
                               [ var "_sim_hdl", var "_clk_hdl", var "dir", next_edge ]
                    , stmt $ (var "bk_trigger_clock_edge") `cCall`
                               [ var "_sim_hdl", var "_clk_hdl", var "dir", var "now" ]
                    , stmt $ (var "bk_advance") `cCall` [ var "_sim_hdl", mkBool False ]
                    , if_cond stop_cond
                          (stmt $ (var "sc_stop") `cCall` [])
                          Nothing
                    ]
                update_outputs =
                    [ comment "update method output ports" (blankLines 0) ] ++
                    [ stmt $ write_port out | out <- outs ]
            in get_clk ++ sample_inputs ++ do_vcd ++ exec ++ update_outputs
        reset_call i =
            let nm = getIdBaseString i
            in stmt $ obj_call "_model_inst" ("reset_" ++ nm) [read_port i]
        clk_fn_decls = map (decl . (handler_type "")) clk_inputs
        clk_fn_defs  = [ define (handler_type name i) (block (clk_stmts i))
                       | i <- clk_inputs
                       ]
        rst_fn_decls = map (decl . (handler_type "")) rst_inputs
        rst_fn_defs  = [ define (handler_type name i) (block [reset_call i])
                       | i <- rst_inputs
                       ]

        -- put it all together
        class_sects   = [ comment "clock and reset inputs" (public clk_rst_decls)
                        , comment "method ports" (public port_decls)
                        , comment "implementation class" (public [sub_mod])
                        , comment "Bluesim kernel state" (private [model_hdl, sim_hdl])
                        , comment "constructor" (public [constructor])
                        , comment "destructor"  (public [destructor])
                        , comment "simulation callbacks" (public [start_of_sim_fn, end_of_sim_fn])
                        , comment "clock and reset handlers" (private (clk_fn_decls ++ rst_fn_decls))
                        ]
        h_fragments   = h_includes ++
                        [ comment "SystemC model definition" $
                          c_macro_class class_name Nothing class_sects
                        ]
        cxx_fragments = cxx_includes ++ [blankLines 1] ++
                        (intersperse (blankLines 1) (clk_fn_defs ++ rst_fn_defs))
        h_contents    = ppReadable $ program [protect_header (name ++ "_systemc") h_fragments]
        cxx_contents  = ppReadable $ program cxx_fragments
    return [(h_name,h_contents), (cxx_name,cxx_contents)]
