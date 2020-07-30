(* synthesize *)
module sysClockedBy_DefaultClock_WrongClock
				 (Clock c1,
				  (* clocked_by="default_clock" *) Bool b,
				  Empty ifc);

   Reg#(Bool) rg <- mkRegU(clocked_by c1);

   rule r;
      rg <= rg && b;
   endrule

endmodule

