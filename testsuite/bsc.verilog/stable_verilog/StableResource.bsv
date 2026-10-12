// -resource-simple: exercises simpleDropEdges' edge pick and colorFw's
// vertex order.  RegFile sub has multiplicity 5; six independent rules
// each read once, so all six can fire simultaneously and one inter-rule
// edge must be dropped (arbitrated), then the remaining uses colored
// onto the five ports.
import RegFile::*;

(* synthesize *)
(* options = "-resource-simple" *)
module sysStableResource();
   RegFile#(Bit#(4), Bit#(8)) rf <- mkRegFile(0, 15);
   Reg#(Bit#(4)) i <- mkReg(0);
   Reg#(Bit#(8)) a <- mkReg(0);
   Reg#(Bit#(8)) b <- mkReg(0);
   Reg#(Bit#(8)) c <- mkReg(0);
   Reg#(Bit#(8)) d <- mkReg(0);
   Reg#(Bit#(8)) e <- mkReg(0);
   Reg#(Bit#(8)) f <- mkReg(0);
   rule r1; a <= rf.sub(i); endrule
   rule r2; b <= rf.sub(i + 1); endrule
   rule r3; c <= rf.sub(i + 2); endrule
   rule r4; d <= rf.sub(i + 3); endrule
   rule r5; e <= rf.sub(i + 4); endrule
   rule r6; f <= rf.sub(i + 5); i <= i + 1; endrule
endmodule
