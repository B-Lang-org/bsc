(* synthesize *)
(* execution_order="r1,r2" *)
module sysExecutionOrderAttrModule();
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bool) rg <- mkReg(True);

   rule r1 (b);
      rg <= True;
   endrule

   rule r2;
      rg <= False;
   endrule
endmodule
