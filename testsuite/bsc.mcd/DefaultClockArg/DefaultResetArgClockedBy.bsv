// When only the default reset is designated, the implicit default clock
// still exists and reset arguments can be clocked by it
// (this was an internal compiler error in an early version of the feature)

(* synthesize *)
(* default_reset = "rst_in" *)
module sysDefaultResetArgClockedBy((* clocked_by = "default_clock" *) Reset rst_in, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + 1;
   endrule
endmodule
