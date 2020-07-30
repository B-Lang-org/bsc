(* synthesize *)
module sysResetBy_DefaultReset ((* reset_by="default_reset" *) Bool b,
				Empty ifc);

   Reg#(Bool) rg <- mkReg(True);

   rule r;
      rg <= rg && b;
   endrule

endmodule

