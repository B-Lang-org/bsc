import Vector::*;

typedef Bit#(4) TD4 ;
typedef Bit#(3) TD3 ;

// TODO:
//   vectors
//   sub interface
//   tagged union
//   all data types ?

typedef struct {
   TD3 x;
   TD4 y;
   TD4 z;
  } TS2 deriving(Bits,Eq);

typedef struct {
   TD3 a;
   TD4 b;
   TS2 c;
  } TS deriving(Bits,Eq);


// (* always_ready, always_enabled *)
interface Test4;
   method Action method1 ( int in1, int in2 );
   method int    method2 ( int in1, int in2 );
   method int    method3 ();
   method ActionValue#(Vector#(3,Vector#(4,TS)))  method4 ( int in1 );

   method Action method5 ( TD4 in1 );
   method int    method6 ( TS in1 );
   method Vector#(3,TS)  method7 ();
   method ActionValue#(TD4)  method8 ();
   method ActionValue#(TD4)  method9 ( TD4 in1 );
   method Vector#(3,Vector#(4,TS))  method10 ();
endinterface

(* synthesize *)
module mkTest4( Test4 );
   return ?;
endmodule
