(* synthesize *)
module sysResetBy_NoReset (Reset r1,
			   (* reset_by="no_reset" *) Bool b,
			   Reset r2,
			   Empty ifc);

   Reg#(Bool) rg1 <- mkReg(True, reset_by r1);
   Reg#(Bool) rg2 <- mkReg(True, reset_by r2);

   rule r1;
      rg1 <= rg1 && b;
   endrule

   rule r2;
      rg2 <= rg2 && b;
   endrule

endmodule

