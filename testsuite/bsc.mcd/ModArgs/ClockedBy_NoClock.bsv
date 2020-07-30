(* synthesize *)
module sysClockedBy_NoClock (Clock c1,
			     (* clocked_by="no_clock" *) Bool b,
			     Clock c2,
			     Empty ifc);

   Reg#(Bool) rg1 <- mkRegU(clocked_by c1);
   Reg#(Bool) rg2 <- mkRegU(clocked_by c2);

   rule r1;
      rg1 <= rg1 && b;
   endrule

   rule r2;
      rg2 <= rg2 && b;
   endrule

endmodule

