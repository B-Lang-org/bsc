interface Ifc;
   method Action m();
endinterface

(* synthesize *)
module sysWarnMethodUrgency (Ifc);

   Reg#(int) rg1 <- mkReg(0);

   rule r;
      rg1 <= rg1 + 1;
   endrule

   method Action m();
      rg1 <= rg1 + 2;
   endmethod

endmodule

