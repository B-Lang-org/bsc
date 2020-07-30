typedef struct  {
  Bit#(32) a;
  Int#(32) b;
  Maybe#(UInt#(32)) c;
} MyStruct deriving(Bits);
 
(* synthesize *)
module mkStructUninitErr3();

   MyStruct foo;
   foo.a = 0;

   rule test;
      $display(foo);
      $finish(0);
   endrule
   
endmodule

