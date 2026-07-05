// The "default_reset_port" attribute provides a port name for the
// implicit default reset (this was the meaning of "default_reset" in
// earlier releases)

(* synthesize *)
(* default_reset_port = "RSTX" *)
module sysDefaultResetRename(Empty);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
