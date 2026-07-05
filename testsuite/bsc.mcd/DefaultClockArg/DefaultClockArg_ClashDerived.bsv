// Error: the derived port name of the designated default clock collides
// with the port name given for another argument

(* synthesize *)
(* default_clock = "clk_in" *)
(* no_default_reset *)
module sysDefaultClockArg_ClashDerived(Clock clk_in, (* port = "CLK_clk_in" *) Bit#(8) d, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + unpack(d);
   endrule
endmodule
