(* synthesize *)
module sysClockedBy_DefaultClock ((* clocked_by="default_clock" *) Bool b,
				  Empty ifc);

   Reg#(Bool) rg <- mkRegU;

   rule r;
      rg <= rg && b;
   endrule

endmodule

