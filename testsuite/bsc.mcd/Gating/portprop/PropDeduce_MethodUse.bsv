interface IFC;
   method Action m();
endinterface

(* synthesize *)
module sysPropDeduce_MethodUse (IFC);
   Reg#(Bool) rg <- mkReg(False);
   method Action m();
      rg <= !rg;
   endmethod
endmodule

