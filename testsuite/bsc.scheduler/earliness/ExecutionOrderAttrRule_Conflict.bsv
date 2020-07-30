(* synthesize *)
module sysExecutionOrderAttrRule_Conflict();
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bool) rg <- mkReg(True);

   rule r1 (b);
      rg <= True;
   endrule

   // has to come after r1 because R/W conflict,
   // but the user has specified the other direction
   (* execution_order="r2,r1" *)
   rule r2;
      b <= False;
      rg <= False;
   endrule
endmodule
