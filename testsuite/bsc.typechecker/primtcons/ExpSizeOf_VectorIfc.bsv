// GitHub Issue #313 (Bluespec Inc Bug 1917): a SizeOf in the length parameter
// of a Vector of subinterfaces confuses GenWrap's method-vs-subinterface
// determination, which happens before typecheck and so cannot reduce
// SizeOf#(Bit#(2)) to 2.  BSC therefore treats 'example' as a method and
// requires its element type to be bitifiable.
//
// This is not fixed by the type-function expansion added in PR #916: the
// example still typechecks fine (see the companion compile_pass), but fails when
// synthesized (compile_verilog_fail_error, T0043).  The test documents the
// current behavior; if #313 is fixed, this should become a compile_verilog_pass.

import Vector::*;

// Using 'SizeOf#(Bit#(2))' triggers the bug; 'typedef 2 Length' would not.
typedef SizeOf#(Bit#(2)) Length;

typedef Bit#(1) Data;

interface Example;
  interface Vector#(Length, WriteOnly#(Data)) example;
endinterface

(* synthesize *)
module mkExample (Example);
  Vector#(Length, Reg#(Data)) ex <- replicateM(mkRegU);
  interface example = ?;
endmodule
