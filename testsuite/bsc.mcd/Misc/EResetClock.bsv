(* synthesize *)
module sysEResetClock(Clock c, Empty ifc);
  Reg#(Bit#(15)) r();
  mkReg#(0) the_r(r, clocked_by c);
endmodule
