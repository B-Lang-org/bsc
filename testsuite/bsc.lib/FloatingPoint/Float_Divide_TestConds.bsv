import FloatingPoint::*;
import Divide::*;
import ClientServer::*;
import GetPut::*;

// ================================================================

(* synthesize *)
module sysFloat_Divide_TestConds(Empty);

   Server#(Tuple2#(UInt#(56),UInt#(28)),Tuple2#(UInt#(28),UInt#(28)))
   int_divider <- mkDivider(1);

   Server#(Tuple3#(Float, Float, RoundMode), Tuple2#(Float,Exception))
   fp_divider <- mkFloatingPointDivider(int_divider);

   Reg #(Bit #(4)) rg_state <- mkReg (0);

   rule rl_div_1_by_1 (rg_state == 0);
      // works:
      $display ("INFO: dividing 1 by 1");
      fp_divider.request.put(tuple3(1, 1, defaultValue));

      rg_state <= 1;
   endrule

   rule rl_div_0_by_1 (rg_state == 2);
      // deadlocks:
      $display ("INFO: dividing 0 by 1");
      fp_divider.request.put(tuple3(0, 1, defaultValue));

      rg_state <= 3;
   endrule

   rule rl_retire (rg_state [0] == 1);
      let r <- fp_divider.response.get();
      $display("result:", fshow(r));
      rg_state <= rg_state + 1;
   endrule

   rule rl_finish (rg_state == 4);
      $display ("Finished");
      $finish (0);
   endrule
endmodule

// ================================================================
