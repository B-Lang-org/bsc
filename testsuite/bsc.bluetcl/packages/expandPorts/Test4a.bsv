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
interface Test4a;
   method ActionValue#(Vector#(3,Vector#(4,TS)))  method4 ( int in1 );
endinterface

(* synthesize *)
module mkTest4a( Test4a );
   return ?;
endmodule
