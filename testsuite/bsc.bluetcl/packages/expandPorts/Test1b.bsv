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
interface Test1b;
   method int    method3 ();
endinterface

(* synthesize *)
module mkTest1b( Test1b );
   return ?;
endmodule

   
