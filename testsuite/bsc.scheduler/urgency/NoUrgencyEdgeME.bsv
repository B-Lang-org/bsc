(* synthesize *)
module mkIgnoredUrgency ();
   Reg#(Bit#(8)) rg1 <- mkRegU;

   Reg#(Bool) b1 <- mkRegU;
   Reg#(Bool) b2 <- mkRegU;
   Reg#(Bool) b3 <- mkRegU;
   Reg#(Bool) b4 <- mkRegU;

   (* descending_urgency = "r1,r2" *)
   rule r1 (b1 && b4);
      rg1 <= rg1 + 1;
   endrule

   (* descending_urgency = "r2,r3" *)
   rule r2 (b2 && !b4);
      rg1 <= rg1 + 2;
   endrule

   (* descending_urgency = "r3,r1" *)
   rule r3 (b3);
      rg1 <= rg1 + 3;
   endrule
endmodule

