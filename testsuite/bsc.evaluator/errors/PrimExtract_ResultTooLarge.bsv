(* synthesize *)
module sysPrimExtract_ResultTooLarge ();
   Reg#(Bit#(32)) src <- mkReg('1);
   Reg#(Bit#(8))  dst <- mkReg(0);

   rule r;
      let hi = 20;
      let lo = 10;
      dst <= src[hi:lo];
   endrule
endmodule
