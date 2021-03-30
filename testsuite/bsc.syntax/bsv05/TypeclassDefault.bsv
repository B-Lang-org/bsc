import FIFO::*;

typeclass Foo#(parameter type a, parameter type b) provisos (Eq#(a))
   dependencies (a determines b);
   function Bool foo(a x1, b x2);
   module mkBar(FIFO#(a)) provisos (Bits#(a,sa));
      Reg#(Bool) r <- mkReg(False);
      rule rr; r <= !r; endrule
      let ff <- mkFIFO;
      return ff;
   endmodule
   function Bool baz(a x1, a x2) = (x1==x2);
endtypeclass
