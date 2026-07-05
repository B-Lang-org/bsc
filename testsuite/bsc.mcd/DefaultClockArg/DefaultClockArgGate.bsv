// The "default_clock_gate" attribute applies to an argument designated
// as the default clock: it gets a gate port, with the given name

(* synthesize *)
(* default_clock = "clk_in", default_clock_gate = "XGATE" *)
(* no_default_reset *)
module sysDefaultClockArgGate(Clock clk_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
