interface Ifc;
   method ActionValue#(Bool) avmeth();
endinterface

(* synthesize *)
module mkCond_AV_NoSplit_Sub(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method ActionValue#(Bool) avmeth();
      return rg;
   endmethod
endmodule

(* synthesize *)
module sysCond_AV_NoSplit();
   Ifc m <- mkCond_AV_NoSplit_Sub;

   rule r;
      Bool b <- m.avmeth;
      if (b)
         $display("True");
      else
         $display("False");
   endrule

   // Confirm that splitting is on by having this rule split
   Reg#(Bool) rg <- mkRegU;
   rule r2;
      if (rg)
         $display("True2");
      else
         $display("False2");
   endrule
endmodule

