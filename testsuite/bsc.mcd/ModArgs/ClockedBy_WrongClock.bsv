(* synthesize *)
module sysClockedBy_WrongClock (Clock c1,
				(* clocked_by="c2" *) Bool b,
				Clock c2,
				Empty ifc);

   Reg#(Bool) rg <- mkRegU(clocked_by c1);

   rule r;
      rg <= rg && b;
   endrule

endmodule

