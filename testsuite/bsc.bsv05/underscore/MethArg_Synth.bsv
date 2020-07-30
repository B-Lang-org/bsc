typedef struct {
  t value;
  } Foo#(numeric type n, type t) deriving(Bits);

interface Bar#(numeric type n, type t);
  method Action bar(Foo#(n, t) _);  // Notice the _, change it to "in" and it compiles.
endinterface

module mkBar (Bar#(n, t))
   provisos ( Bits#(t, k)
                  , Bits#(Foo#(n, t), k) );
   method Action bar(Foo#(n, t) in);
   endmethod
endmodule

(* synthesize *)
module synBar (Bar#(1, Bool));
  Bar#(1, Bool) bar <- mkBar;
  return bar;
endmodule

