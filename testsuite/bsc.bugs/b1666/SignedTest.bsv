int default_rate = 9600;

(* synthesize *)
module mkSignedTest_Sub# (parameter int clk_mhz) (Reg#(Int#(32)));
   Reg#(Int#(32)) period <- mkReg((clk_mhz * 1000) / default_rate);
   return period;
endmodule

(* synthesize *)
module sysSignedTest ();

   Reg#(Int#(32)) rg <- mkSignedTest_Sub(default_rate * 2);

   Reg#(Bool) done <- mkReg(False);

   rule do_test (!done);
      $display("rg = %d", rg);
      done <= True;
   endrule

   rule do_finish (done);
      $finish(0);
   endrule

endmodule
