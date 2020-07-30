(* synthesize *)
module sysSameCanFire ();
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bool) y <- mkReg(False);
   Reg#(Bool) x <- mkReg(False);

   rule r1 (b);
      x <= True;
      b <= False;
   endrule

   rule r2 (b);
      y <= True;
   endrule

   rule r3 (!b);
      $finish(0);
   endrule
endmodule

