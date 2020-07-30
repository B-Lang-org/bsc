(* synthesize *)
module sysResetBy_DefaultReset_WrongReset
				 (Reset r1,
				  (* reset_by="default_reset" *) Bool b,
				  Empty ifc);

   Reg#(Bool) rg <- mkReg(True, reset_by r1);

   rule r;
      rg <= rg && b;
   endrule

endmodule

