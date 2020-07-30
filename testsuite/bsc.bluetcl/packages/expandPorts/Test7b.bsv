import Vector::*;

typedef Bit#(4) TD ;

// TODO:
//   vectors
//   sub interface
//   tagged union
//   all data types ?

typedef struct {
   TD a;
   TD b;
   TD c;
  } TS deriving(Bits,Eq);

// (* always_ready, always_enabled *)
interface TestN;
   method Action method1 ( int in1, int in2 );
   method int    method2 ( int in1, int in2 );
endinterface

interface Test7b;
   interface Vector#(2,TestN) ifcA;
endinterface

(* synthesize *)
module mkTest7b#(Clock c1, Int#(4) pIn)( Test7b );
   return ?;
endmodule
