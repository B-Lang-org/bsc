package Check;
import TBase::*;
import PkgRefs::*;
import DA::*;
import DB::*;
import L0::*;
import L1::*;
import L2::*;
import L3::*;
import L4::*;
import L5::*;
import L6::*;
import L7::*;
function Bit#(8) chainForce(Box#(Box#(Y0)) x) = getC(x);
(* synthesize *)
module sysCheck(Empty);
   rule r;
      X0#(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) xv = X0 { f: 8'd100 };
      Box#(Box#(Y0)) bv = Box { g: Box { g: Y0 { f: 8'd77 } } };
      $display("k0=%0d", l0_use0(xv));
      $display("k1=%0d", l1_use0(xv));
      $display("k2=%0d", l2_use0(xv));
      $display("k3=%0d", l3_use0(xv));
      $display("k4=%0d", l4_use0(xv));
      $display("k5=%0d", l5_use0(xv));
      $display("k6=%0d", l6_use0(xv));
      $display("k7=%0d", l7_use0(xv));
      $display("r=%0d c=%0d m=%0d", ref1(W0 { f: 8'd9 }), chainForce(bv), da0(bv));
      $finish(0);
   endrule
endmodule
endpackage
