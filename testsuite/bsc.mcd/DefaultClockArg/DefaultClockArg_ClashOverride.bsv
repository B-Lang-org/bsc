// Error: the port name given for the designated default clock collides
// with the derived port name of another clock argument

(* synthesize *)
(* default_clock = "clk_a", default_clock_osc = "CLK_clk_b" *)
(* no_default_reset *)
module sysDefaultClockArg_ClashOverride(Clock clk_a, Clock clk_b, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
