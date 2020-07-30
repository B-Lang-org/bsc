module mkTest(Empty);
   Reg#(Bool) b();
   mkReg#(False) the_b(b);

   rule foo;
      let x = asReg(b);
      x <= True;
   endrule
endmodule
