import Clocks::*;

(* synthesize *)
module sysEResetMux2(Clock c, Reset r1, Reset r2, SyncBitIfc#(Bit#(1)) out_ifc);
  Reg#(Bool) b <- mkReg(False);
 
  // illegally muxed reset
  Reset r = b ? r1 : r2;
  
  SyncBitIfc#(Bit#(1)) ifc();
  mkSyncBitToCC#(c, r) the_ifc(ifc);
  
  return ifc; 
endmodule
