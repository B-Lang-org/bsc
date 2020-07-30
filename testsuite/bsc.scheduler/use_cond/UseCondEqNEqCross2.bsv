(* synthesize *)
module sysUseCondEqNEqCross2();
   
   Reg#(UInt#(16)) a <- mkRegU;   
   
   Reg#(Bit#(32)) source1 <- mkRegU;
   Reg#(Bit#(32)) source2 <- mkRegU;
   Reg#(Bit#(32)) dest <- mkRegU;
   
   let shared = (a != 1) ? source1 : source2;
   
   (* conflict_free="test1, test2" *)
   (* execution_order="test0, test1, test2" *)
   rule test1;
      source1 <= 0;
      source2 <= 0;
   endrule
   
   rule test0;
      $display(shared);
   endrule
   
   rule test2;
      dest <= (a == 1) ? shared : 2;
   endrule
   
endmodule

   
