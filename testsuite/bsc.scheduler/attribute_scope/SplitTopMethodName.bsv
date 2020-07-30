interface Ifc;
   method Action mymethod();
endinterface

(* synthesize *)
module sysSplitTopMethodName (Ifc);
   Reg#(Bool) b <- mkRegU;
   Reg#(UInt#(16)) rg <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   (* descending_urgency = "mymethod, r" *)
   rule r;
      rg <= rg + 1;
   endrule

   method Action mymethod();
      (* split *)
      if (b)
         rg <= rg + 2;
      else
         rg2 <= rg2 + 1;
   endmethod
endmodule
