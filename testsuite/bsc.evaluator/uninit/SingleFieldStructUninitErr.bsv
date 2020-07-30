import Complex::*;

typedef struct {
   Complex#(Integer) my_complex;
   } MyComplex deriving(Eq);

(* synthesize *)
module mkSingleFieldStructUninitErr();
   MyComplex foo;
   foo.my_complex.rel = 0;
   
   rule test;
      $display(foo == foo);
      $finish(0);
   endrule
   
endmodule

		
