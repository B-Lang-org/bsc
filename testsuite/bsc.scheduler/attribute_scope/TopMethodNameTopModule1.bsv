interface Ifc;
   method Action mymethod();
endinterface

(* synthesize *)
module sysTopMethodNameTopModule1 (Ifc);
   Reg#(UInt#(16)) rg <- mkRegU;

   (* descending_urgency = "mymethod, r" *)
   rule r;
      rg <= rg + 1;
   endrule

   method Action mymethod();
      rg <= rg + 2;
   endmethod
endmodule
