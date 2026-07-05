// Error: with an empty clock_prefix, the designated default clock
// argument's port is its bare name, which collides with a rename of
// another argument to the same name

(* synthesize *)
(* default_clock = "clk_in", clock_prefix = "" *)
(* no_default_reset *)
module sysDefaultClockArg_ClashEmptyPrefix(Clock clk_in, (* port = "clk_in" *) Bit#(8) d, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + unpack(d);
   endrule
endmodule
