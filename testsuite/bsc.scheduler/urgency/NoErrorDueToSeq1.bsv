// Test that there is no urgency warning when a sequence of edges
// restricts the order

(* synthesize *)
module mkNoErrorDueToSeq1 ();
   Reg#(Bit#(8)) rg1 <- mkRegU;
   Reg#(Bit#(8)) rg2 <- mkRegU;

   Reg#(Bool) b1 <- mkRegU;
   Reg#(Bool) b2 <- mkRegU;
   Reg#(Bool) b3 <- mkRegU;
   
   (* descending_urgency = "r1,r2" *)
   rule r1 (b1);
      rg1 <= rg1 + 1;
      rg2 <= rg2 + 1;
   endrule

   (* descending_urgency = "r2,r3" *)
   rule r2 (b2);
      rg2 <= rg2 - 1;
   endrule
   
   rule r3 (b3);
      rg1 <= rg1 - 1;
   endrule
endmodule
