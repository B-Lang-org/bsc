
// Test with subinterfaces

interface Ifc;
   method Action mymethod1();
   interface SubIfc sub;
endinterface

interface SubIfc;
   method Action mymethod2();
endinterface

(* synthesize *)
module sysTopMethodNameSubModule (Ifc);
   Reg#(UInt#(16)) rg1 <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   Empty m <- mkMod(rg1, rg2);

   method Action mymethod1();
      rg1 <= rg1 + 2;
   endmethod

   interface SubIfc sub;
      method Action mymethod2();
         rg2 <= rg2 + 2;
      endmethod
   endinterface
endmodule

module mkMod(Reg#(UInt#(16)) rg1, Reg#(UInt#(16)) rg2, Empty ifc);
   (* descending_urgency = "sub_mymethod2, r" *)
   (* descending_urgency = "mymethod1, r" *)
   rule r;
      rg1 <= rg1 + 1;
      rg2 <= rg2 + 1;
   endrule
endmodule
