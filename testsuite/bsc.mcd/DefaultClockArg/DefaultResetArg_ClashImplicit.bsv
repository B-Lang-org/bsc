// Error: the port name given for the designated default reset collides
// with the port of the implicit default clock

(* synthesize *)
(* default_reset = "rst_in", default_reset_port = "CLK" *)
module sysDefaultResetArg_ClashImplicit(Reset rst_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
