interface Ifc;
   method Action m(Bool b);
endinterface

(* synthesize *)
module sysCond_MethodArg_NoSplit(Ifc);
   // Confirm that splitting is on by having this rule split
   Reg#(Bool) rg <- mkRegU;
   rule r2;
      if (rg)
         $display("True2");
      else
         $display("False2");
   endrule

   method Action m(Bool b);
      if (b)
         $display("True");
      else
         $display("False");
   endmethod
endmodule

