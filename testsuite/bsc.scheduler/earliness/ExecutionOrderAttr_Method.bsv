interface Ifc;
   method Action m();
endinterface

(* synthesize *)
(* execution_order="r1,m" *)
module sysExecutionOrderAttr_Method (Ifc);
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bool) rg <- mkReg(True);

   rule r1 (b);
      rg <= True;
   endrule

   method Action m();
      rg <= False;
   endmethod
endmodule
