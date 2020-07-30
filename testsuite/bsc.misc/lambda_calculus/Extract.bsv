(* synthesize *)
module sysExtract();

   // static extract

   Reg#(Bit#(12)) src1 <- mkRegU;
   Reg#(Bit#(8))  snk1 <- mkRegU;

   rule do_static;
      snk1 <= src1[9:2];
   endrule

   // dynamic extract

   Reg#(Bit#(12)) src2 <- mkRegU;
   Reg#(Bit#(8))  snk2 <- mkRegU;

   Reg#(Bit#(4))  hi_idx <- mkRegU;
   Reg#(Bit#(4))  lo_idx <- mkRegU;

   rule do_dynamic;
      snk2 <= src2[hi_idx:lo_idx];
   endrule

endmodule

