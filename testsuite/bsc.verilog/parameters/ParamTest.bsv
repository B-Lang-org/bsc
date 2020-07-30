
interface SubIFC;
   method Action set (Bit#(16) val);
endinterface

// This module is set up to have several ports and parameters,
// hoping to catch any way that the order or ports and parameters
// could be mixed up in the compiler, while also testing generation
// to Verilog for the parameters.

(* synthesize *)
module mkParamTestSub #(Bit#(8) w,
			parameter Bool x,
			Bit#(16) y,
			parameter Bit#(10) z)
                       (SubIFC);

   // have a register with reset, to avoid display during reset
   Reg#(Bool) r <- mkReg(False);

   method Action set (Bit#(16) val);
      let coef = x ? 2 : 3;
      Bit#(16) res = coef * (zeroExtend(w) + zeroExtend(z));
      if (res > y)
	 res = res - val;
      $display("res = %d", res);
      r <= True;
   endmethod

endmodule


// Test that a parent module can provide values and successfully
// simulate in Verilog and Bluesim

(* synthesize *)
module sysParamTest ();
   SubIFC sub <- mkParamTestSub (6, True, 5, 4);

   Reg#(Bool) done <- mkReg(False);

   rule r_display (!done);
      sub.set(3);
      done <= True;
   endrule

   rule r_finish (done);
      $finish(0);
   endrule

endmodule


