import FIFOF :: *;

(* synthesize *)
module sysSharedPortsFIFO();
   FIFOF#(Bit#(8)) f <- mkFIFOF;

   Reg#(Bit#(16)) rg <- mkReg(0);

   rule do_enq;
      f.enq(0);
      // make the rules conflict via a shared register
      rg <= rg - 1;
   endrule

   rule do_otherwise (! f.notFull);
      // make the rules conflict via a shared register
      rg <= rg + 1;
   endrule
endmodule
