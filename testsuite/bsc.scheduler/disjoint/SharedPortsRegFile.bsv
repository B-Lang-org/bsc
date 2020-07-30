import RegFile :: *;

(* synthesize *)
module sysSharedPortsRegFile();
   RegFile#(Bit#(3), Bool) rf <- mkRegFileFull;
   Reg#(Bit#(3)) idx1 <- mkReg(0);
   Reg#(Bit#(3)) idx2 <- mkReg(1);

   Reg#(Bit#(16)) rg <- mkReg(0);

   rule do1 (rf.sub(idx1));
      // make the rules conflict via a shared register
      rg <= rg - 1;
   endrule

   rule do2 (! rf.sub(idx2));
      // make the rules conflict via a shared register
      rg <= rg + 1;
   endrule
endmodule
