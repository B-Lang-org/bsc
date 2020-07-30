(* synthesize *)
module sysMultiArityConcat();
   Reg#(Bit#(3)) src1 <- mkRegU;
   Reg#(Bit#(4)) src2 <- mkRegU;
   Reg#(Bit#(5)) src3 <- mkRegU;

   Reg#(Bit#(12)) snk <- mkRegU;

   rule d;
      snk <= { src1, src2, src3 };
   endrule
endmodule

