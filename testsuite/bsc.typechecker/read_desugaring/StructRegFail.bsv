typedef struct {
   Reg#(a) a;
   Reg#(b) b;
} Foo#(type a, type b);

(* synthesize *)
module sysStructRegFail();
   Reg#(Bit#(67)) a <- mkReg(0);
   Reg#(Maybe#(Bool)) b <- mkReg(Invalid);
   
   Foo#(Bit#(67), Maybe#(Bool)) foo = Foo { a : asIfc(a), b : asIfc(b) };
   
   rule test;
      if(!isValid(foo.a)) $display("%b", foo.a);
      $finish(0);
   endrule
   
endmodule
