(* synthesize *)
module sysPrimExtract_ResultTooLarge_Literal ();
   Reg#(Bit#(32)) src <- mkReg('1);
   Reg#(Bit#(8))  dst <- mkReg(0);

   rule r;
      dst <= src[20:10];
   endrule
endmodule
