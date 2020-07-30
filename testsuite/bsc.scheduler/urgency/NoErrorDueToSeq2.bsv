// Test that there is no urgency warning when a sequence of edges
// restricts the order

(* synthesize *)
module mkNoErrorDueToSeq2 ();
   Reg#(Bit#(8)) rg <- mkRegU;
   RWire#(Bool) rw1 <- mkRWire;
   RWire#(Bool) rw2 <- mkRWire;

   //(* descending_urgency = "r3,r1" *)
   rule r1;
      rg <= rg + 1;
      rw1.wset(True);
   endrule

   rule r2;
      rw2.wset(!isValid(rw1.wget));
   endrule
   
   rule r3 (isValid(rw2.wget));
      rg <= rg - 1;
   endrule
endmodule
