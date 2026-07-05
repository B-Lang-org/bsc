// Test the "default_clock" and "default_reset" attributes, which designate
// module arguments as the module's default clock and reset

interface Ifc;
   method Action poke();
   method UInt#(8) count();
endinterface

(* synthesize *)
(* default_clock = "clk_in", default_reset = "rst_in" *)
module mkDefaultClockArg(Clock clk_in, Reset rst_in, Ifc ifc);
   // uses the default clock (clk_in) and reset (rst_in)
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule

   // a stub method with no clocked state defaults to clk_in
   // (with no_default_clock, it would be associated with noClock
   // and its body would be silently dropped)
   method Action poke();
      $display("poke fired");
   endmethod

   method count = ctr;
endmodule

(* synthesize *)
module sysDefaultClockArg();
   Clock c <- exposeCurrentClock;
   Reset r <- exposeCurrentReset;
   Ifc dut <- mkDefaultClockArg(c, r);

   Reg#(UInt#(8)) cycle <- mkReg(0);

   rule r_count;
      cycle <= cycle + 1;
   endrule

   rule r_poke (cycle == 2);
      dut.poke();
   endrule

   rule r_done (cycle == 5);
      $display("count = %0d", dut.count());
      $finish(0);
   endrule
endmodule
