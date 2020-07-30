interface IFC;
   method Action m();
endinterface

(* synthesize *)
module sysPropDeduce_RuleAndMethodShareUse (IFC);

   Reg#(Bool) rg <- mkReg(False);
   Action act = action
		   $display("rg = ", rg);
		   rg <= !rg;
		endaction;

   rule r;
      act;
   endrule

   method Action m();
      act;
   endmethod

endmodule
