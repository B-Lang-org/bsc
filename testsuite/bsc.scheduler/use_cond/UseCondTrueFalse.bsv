(* synthesize *)
module sysUseCondTrueFalse();
   
   Reg#(Bool) a <- mkRegU;   
   Reg#(Bool) b <- mkRegU;
   Reg#(Bool) c <- mkRegU;
   
   Reg#(Bit#(32)) source <- mkRegU;
   Reg#(Bit#(32)) dest1 <- mkRegU;
   Reg#(Bit#(32)) dest2 <- mkRegU;
   
   (* conflict_free="test1, test2" *)
   (* execution_order="test1, test2" *)
   rule test1;
      source <= 0;
   endrule

   rule test2;
      dest1 <= a ? (!b ? source : 0) : 2;
      dest2 <= a ? (!c ? source : 0) : 1;
   endrule
   
endmodule

   
