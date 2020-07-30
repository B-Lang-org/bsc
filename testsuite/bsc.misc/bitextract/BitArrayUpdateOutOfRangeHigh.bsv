(* synthesize *)
module sysPrimBitArrayUpdate_IndexTooLarge ();
   Reg#(Bit#(8))  dst <- mkReg(0);
   rule r;
      Bit#(8) val;
      for (Integer i=0; i<=8; i=i+1)
         val[i] = 1;
      dst <= val;
   endrule
endmodule
