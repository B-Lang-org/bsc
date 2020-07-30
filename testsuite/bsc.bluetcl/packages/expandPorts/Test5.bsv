import Vector::*;

typedef Bit#(4) TD4 ;
typedef Bit#(3) TD3 ;

// TODO:
//   vectors
//   sub interface
//   tagged union
//   all data types ?
typedef enum { ValA, ValB, ValC=11 } TEnum deriving(Bits,Eq);

typedef union tagged {
   TD3 X;
   TD4 Y;
   TD4 Z;
  } TS2 deriving(Bits,Eq);

typedef struct {
   TD3 a;
   TD4 b;
   TS2 c;
  } TS deriving(Bits,Eq);


// (* always_ready, always_enabled *)
interface Test5;
   method Action method1 ( int in1, int in2 );
   method int    method2 ( int in1, int in2 );
   method int    method3 ();
   method ActionValue#(TS)  method4 ( int in1 );

   method Action method5 ( TD4 in1 );
   method int    method6 ( TS in1 );
   method TS  method7 ();
   method ActionValue#(TD4)  method8 ();
   method ActionValue#(TD4)  method9 ( TD4 in1 );
   method Vector#(3,TS)  method10 ();
   method TEnum  method20 ();
endinterface

(* synthesize *)
module mkTest5( Test5 );
   return ?;
endmodule

   
