// With an empty clock_prefix, a designated default clock argument's
// port is named exactly like the argument

(* synthesize *)
(* default_clock = "clk_in", clock_prefix = "" *)
(* no_default_reset *)
module sysDefaultClockArgEmptyPrefix(Clock clk_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
