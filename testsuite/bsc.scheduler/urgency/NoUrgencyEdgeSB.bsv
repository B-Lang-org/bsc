(* synthesize *)
module mkIgnoredUrgency ();
   Reg#(Bit#(8)) rg1 <- mkRegU;
   Reg#(Bit#(8)) rg2 <- mkRegU;
   Reg#(Bit#(8)) rg3 <- mkRegU;

   // state to make the rules SB
   Reg#(Bit#(8)) rgA <- mkRegU;
   Reg#(Bit#(8)) rgB <- mkRegU;
   Reg#(Bit#(8)) rgC <- mkRegU;
   Reg#(Bit#(8)) rgD <- mkRegU;
   
   (* descending_urgency = "r1,r2" *)
   rule r1;
      rg1 <= rg1 + 1;
      rgA <= rgB + rgD;
   endrule

   (* descending_urgency = "r2,r3" *)
   rule r2;
      rg2 <= rg2 + 1;
      rgB <= rgC;
   endrule

   (* descending_urgency = "r3,r1" *)
   rule r3;
      rg3 <= rg3 + 1;
      rgC <= 0;
      rgD <= 0;
   endrule
endmodule

