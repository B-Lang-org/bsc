import FloatingPoint::*;
import SquareRoot::*;
import ClientServer::*;
import GetPut::*;

// ================================================================

(* synthesize *)
module sysFloat_SquareRoot_TestConds(Empty);

   Server#(UInt#(60),Tuple2#(UInt#(60),Bool))
   int_squarerooter <- mkSquareRooter(1);

   Server#(Tuple2#(Float, RoundMode), Tuple2#(Float,Exception))
   fp_squarerooter <- mkFloatingPointSquareRooter(int_squarerooter);

   Reg #(Bit #(4)) rg_state <- mkReg (0);

   rule rl_sqrt_1 (rg_state == 0);
      // works:
      $display ("INFO: square root of 1");
      fp_squarerooter.request.put(tuple2(1, defaultValue));

      rg_state <= 1;
   endrule

   rule rl_sqrt_neg_1 (rg_state == 2);
      // deadlocks:
      $display ("INFO: square root of -1");
      fp_squarerooter.request.put(tuple2(-1, defaultValue));

      rg_state <= 3;
   endrule

   rule rl_retire (rg_state [0] == 1);
      let r <- fp_squarerooter.response.get();
      $display("result:", fshow(r));
      rg_state <= rg_state + 1;
   endrule

   rule rl_finish (rg_state == 4);
      $display ("Finished");
      $finish (0);
   endrule
endmodule

// ================================================================
