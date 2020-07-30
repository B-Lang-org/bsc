(* synthesize *)
module mkIgnoredUrgency ();
   Reg#(Bit#(8)) rg1 <- mkRegU;
   Reg#(Bit#(8)) rg2 <- mkRegU;
   Reg#(Bit#(8)) rg3 <- mkRegU;

   (* descending_urgency = "r1,r2" *)
   rule r1;
      rg1 <= rg1 + 1;
   endrule

   (* descending_urgency = "r2,r3" *)
   rule r2;
      rg2 <= rg2 + 1;
   endrule

   (* descending_urgency = "r3,r1" *)
   rule r3;
      rg3 <= rg3 + 1;
   endrule
endmodule

