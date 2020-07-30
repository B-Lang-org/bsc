(* synthesize *)
module sysEResetMux1(Reset r1, Reset r2, Empty ifc);
  Reg#(Bool) b <- mkReg(False);
 
  // illegally muxed reset
  Reset r = b ? r1 : r2;
  
  Reg#(Bit#(32)) x();
  mkRegU the_x(x, reset_by r);

endmodule
