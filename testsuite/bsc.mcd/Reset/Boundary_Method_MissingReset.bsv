import Clocks::*;

interface Ifc;
   method Action meth1(Bool x);
endinterface

(* synthesize *)
module sysBoundary_Method_MissingReset (Ifc);
   Reset rst1 <- mkInitialReset(2);

   Reg#(Bool) rg1 <- mkReg(False, reset_by rst1);

   method Action meth1(Bool x);
      rg1 <= x;
   endmethod
endmodule

