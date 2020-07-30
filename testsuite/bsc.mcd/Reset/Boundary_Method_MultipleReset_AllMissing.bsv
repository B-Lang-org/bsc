import Clocks::*;

interface Ifc;
   method Action meth1(Bool x);
endinterface

(* synthesize *)
module sysBoundary_Method_MultipleReset_AllMissing (Ifc);
   Reset rst1 <- mkInitialReset(2);
   Reset rst2 <- mkInitialReset(3);

   Reg#(Bool) rg1 <- mkReg(False, reset_by rst1);
   Reg#(Bool) rg2 <- mkReg(False, reset_by rst2);

   method Action meth1(Bool x);
      rg1 <= x;
      rg2 <= x;
   endmethod
endmodule

