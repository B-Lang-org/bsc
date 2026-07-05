// Designate only the default reset; the implicit default clock remains

(* synthesize *)
(* default_reset = "rst_in" *)
module sysDefaultResetArgOnly(Reset rst_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
