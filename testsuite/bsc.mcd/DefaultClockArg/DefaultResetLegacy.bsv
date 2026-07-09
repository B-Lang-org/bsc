// Error: a "default_reset" value which does not name an argument
// (in earlier releases, this attribute provided a port name for the
// implicit default reset; the error message should point users at
// the "default_reset_port" attribute)

(* synthesize *)
(* default_reset = "RSTX" *)
module sysDefaultResetLegacy(Empty);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
