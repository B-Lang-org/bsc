(* synthesize *)
module sysExecutionOrderAttrRule();
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bool) rg <- mkReg(True);

   rule r1 (b);
      rg <= True;
   endrule

   (* execution_order="r1,r2" *)
   rule r2;
      rg <= False;
   endrule
endmodule
