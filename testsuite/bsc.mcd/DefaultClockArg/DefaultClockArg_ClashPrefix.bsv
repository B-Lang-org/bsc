// Error: with a lower-case clock_prefix, the derived port name of the
// designated default clock argument collides with a data argument's name

(* synthesize *)
(* default_clock = "a", clock_prefix = "clk" *)
(* no_default_reset *)
module sysDefaultClockArg_ClashPrefix(Clock a, Bit#(8) clk_a, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + unpack(clk_a);
   endrule
endmodule
