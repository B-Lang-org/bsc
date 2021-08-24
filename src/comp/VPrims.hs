module VPrims(viWidth, vMux, vPriMux, vPriEnc, verilogInstancePrefix) where
import Util(itos)
import Verilog

verilogInstancePrefix :: String
verilogInstancePrefix = ""

vMux :: Integer -> VModule
vMux = vMuxP True


vPriMux :: Integer -> VModule
vPriMux = vMuxP False

vPriEnc :: Bool -> Integer -> VModule
vPriEnc _ = vMuxP False



vMuxP :: Bool -> Integer -> VModule
vMuxP parallel n = VModule { vm_name = (mkVId ("Mux_" ++ itos n)),
                             vm_comments = comments,
                             vm_ports = [(args,[])],
                             vm_body = [regdecl,outassign,body] }
  where
        comments = [] -- XXX room to add comments
        args = param : out : iss
        param = VAParameter viWidth Nothing (VEConst 1)
        out = VAOutput viOut rng
        iss = concatMap (\ n -> [VAInput (i n) rng, VAInput (s n) Nothing]) ns
        hi = mkVEOp w VSub one
        lo = zero
        w = VEVar viWidth
        rng = Just (hi, lo)
        i n = mkVId ("in_" ++ itos n)
        s n = mkVId ("s_" ++ itos n)
        outassign = VMAssign (VLId viOut) (VEVar viOutReg)
        regdecl = VMDecl (VVDecl VDReg rng [(VVar viOutReg)])
        body = VMStmt{ vi_simulation_only = False,
                       vi_body = Valways $ VAt (slist (ins ++ (init sels)))  $
                                 Vcase { vs_case_expr = onetickbone,
                                         vs_case_arms = arms (VLId viOutReg) (zip (map VEVar sels) (map VEVar ins)),
                                         vs_parallel = parallel,
                                         vs_full = True
                                       }
                     }
        ns = [0..n-1]
        sels = map s ns
        ins = map i ns



onetickbone :: VExpr
onetickbone = VEWConst (mkVId "1") 1 2 1

arms :: VLValue -> [(VExpr,VExpr)] -> [VCaseArm]
arms x [] = []  -- shouldn't happen
arms lhs [(c,e)] = [VDefault (VAssign lhs e)]
arms lhs ((c,e) : ces) =
    (VCaseArm  [c] (VAssign lhs e)) : arms lhs ces

slist :: [VId] -> VEventExpr
slist vars = foldr1 VEEOr (map (VEE . VEVar) vars)

viWidth :: VId
viWidth = mkVId "width"

viOut :: VId
viOut = mkVId "out"

viOutReg :: VId
viOutReg = mkVId "outreg"


zero, one :: VExpr
zero = VEConst 0
one = VEConst 1
