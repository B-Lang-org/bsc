(* synthesize *)
module sysUseCondNEqVars2();
   
   Reg#(UInt#(16)) a <- mkRegU;   
   Reg#(UInt#(16)) b <- mkRegU;
   
   Reg#(Bit#(32)) source <- mkRegU;
   Reg#(Bit#(32)) dest1 <- mkRegU;
   Reg#(Bit#(32)) dest2 <- mkRegU;
   
   (* conflict_free="test1, test2" *)
   (* execution_order="test1, test2" *)
   rule test1;
      source <= 0;
   endrule

   rule test2;
      dest1 <= (a != 0) ? ((b != 3) ? source : 5) : 7;
      dest2 <= (a != 2) ? ((b != 3) ? source : 6) : 9;
   endrule
   
endmodule

   
