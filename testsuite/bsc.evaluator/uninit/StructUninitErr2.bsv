typedef struct  {
  Bit#(32) a;
  Int#(32) b;
  Maybe#(UInt#(32)) c;
} MyStruct;
 
(* synthesize *)
module mkStructUninitErr2();

   MyStruct foo;
   foo.a = 0;

   rule test;
      $display(foo.c);
      $finish(0);
   endrule
   
endmodule

