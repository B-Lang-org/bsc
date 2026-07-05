// Error: when only the default reset is designated, the implicit default
// clock port is the bare (here, lower-case) clock prefix, which collides
// with a data argument's name

(* synthesize *)
(* default_reset = "rst_in", clock_prefix = "ck" *)
module sysDefaultResetArg_ClashBarePrefix(Reset rst_in, Bit#(8) ck, Empty ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   rule r_tick;
      ctr <= ctr + unpack(ck);
   endrule
endmodule
