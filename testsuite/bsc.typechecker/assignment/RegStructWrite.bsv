typedef struct {
   a a;
   b b;
} Foo#(type a, type b) 
  deriving(Eq, Bits); 

(* synthesize *)
module mkRegStructWrite();   
   Reg#(Foo#(Bool, Maybe#(Bool))) foo <- mkReg(Foo { a : True, b : Nothing });
   
   rule test;
      foo.a <= True;
      foo.b <= Just (False);
   endrule
   
endmodule
