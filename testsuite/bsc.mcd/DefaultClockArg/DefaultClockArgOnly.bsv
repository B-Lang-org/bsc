// Designate only the default clock; the implicit default reset remains
// (and is associated with the designated clock)

(* synthesize *)
(* default_clock = "clk_in" *)
module sysDefaultClockArgOnly(Clock clk_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
