// This tests a bug in which PrimPriMux was changed to check the second
// condition first if it is simple and the first condition is not.
// (NSS = Non-Simple, Simple)

module mkPrimPriMuxNSS (Empty);

   Reg#(Bool) b();
   mkReg#(False) the_b(b);

   // mechanism to set up the PrimPriMux in ASyntax

   Reg#(int) v();
   mkReg#(0) the_v(v);

   Reg#(int) v2();
   mkReg#(20) the_v2(v2);

   Reg#(Bool) p();
   mkReg#(True) the_p(p);

   rule r1 (p);
      v <= v + 1;
      b <= True;
   endrule

   rule r2 (p);
      // needed to give the register write a complex condition
      if (v2 > 17)
	 v <= 32;
      b <= True;
   endrule

   // mechanism to create output to test the codegen
   rule r3 (b);
      $display("Result: %d", v);
      $finish(0);
   endrule
   
endmodule
