typedef struct {
   Reg#(a) a;
   Reg#(b) b;
} Foo#(type a, type b);

module mkStructRegWrite();
   Reg#(Bool) a <- mkReg(False);
   Reg#(Maybe#(Bool)) b <- mkReg(Nothing);
   
   Foo#(Bool, Maybe#(Bool)) foo = Foo { a : asIfc(a), b : asIfc(b) };
   
   rule test;
      foo.a <= True;
      foo.b <= Just (False);
   endrule
   
endmodule
