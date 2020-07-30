
// Test with subinterfaces

interface Ifc;
   method Action mymethod1();
   interface SubIfc sub;
endinterface

interface SubIfc;
   method Action mymethod2();
endinterface

(* synthesize *)
module sysTopMethodNameSubModuleClash (Ifc);
   Ifc m <- mkMod();

   method Action mymethod1();
      m.mymethod1();
   endmethod

   interface SubIfc sub;
      method Action mymethod2();
         m.sub.mymethod2();
      endmethod
   endinterface
endmodule

module mkMod(Ifc);
   Reg#(UInt#(16)) rg1 <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   (* descending_urgency = "sub_mymethod2, r" *)
   (* descending_urgency = "mymethod1, r" *)
   rule r;
      rg1 <= rg1 + 1;
      rg2 <= rg2 + 1;
   endrule

   method Action mymethod1();
      rg1 <= rg1 + 2;
   endmethod

   interface SubIfc sub;
      method Action mymethod2();
         rg2 <= rg2 + 2;
      endmethod
   endinterface
endmodule
