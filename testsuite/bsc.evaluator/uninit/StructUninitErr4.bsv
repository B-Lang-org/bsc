typedef struct  {
  Bit#(32) a;
  Int#(32) b;
  Maybe#(UInt#(32)) c;
} MyStruct deriving(Bits);
 
(* synthesize *)
module mkStructUninitErr4();

   MyStruct foo;
   if (False)
      foo.a = 0;

   rule test;
      $display(foo);
      $finish(0);
   endrule
   
endmodule

