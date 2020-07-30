(* synthesize *)
module sysEClockMux1(Clock c1, Clock c2, Empty ifc);
  Reg#(Bool) b <- mkReg(False);
 
  // illegally muxed clock
  Clock c = b ? c1 : c2;
  
  Reg#(Bit#(32)) x();
  mkRegU the_x(x, clocked_by c);

endmodule
