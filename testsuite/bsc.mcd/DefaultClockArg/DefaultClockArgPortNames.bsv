// The attributes which name the default clock and reset ports apply to
// arguments designated as the default clock and reset: the argument name
// is used inside the module and the given names are used for the ports
// on the boundary

(* synthesize *)
(* default_clock = "clk_in", default_clock_osc = "XCLK" *)
(* default_reset = "rst_in", default_reset_port = "XRST" *)
module sysDefaultClockArgPortNames(Clock clk_in, Reset rst_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
