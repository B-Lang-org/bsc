import Clocks::*;

(* synthesize *)
module mkModulePort_ResetMux #(Bool b)();

   Reset rst1 <- mkInitialReset(7);
   Reset rst2 <- mkInitialReset(2);

   let rst = b ? rst1 : rst2;

   Reg#(Bit#(32)) x <- mkReg(0, reset_by rst);

   rule r;
      x <= x + 1;
      $display("X = ", x);
      if (x > 17)
	 $finish(0);
   endrule

endmodule

