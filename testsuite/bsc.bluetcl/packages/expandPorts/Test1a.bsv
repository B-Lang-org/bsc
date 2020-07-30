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

interface Test1a;
   (* ready = "amIready" *) method TS     method2 ( int in1, int in2 );
   (*always_ready*)         method Action method3 ( int in1, TS  in2 );
   (*always_enabled*)       method int method4 ();
endinterface

(* synthesize *)
module mkTest1a( Test1a );
   return ?;
endmodule

   
