// Regression test for a method-multiplicity port-mapping bug (see PR #928).
//
// When an imported (BVI) method has multiplicity > 1 and more than one
// argument, the map between the method-internal port names and the actual
// Verilog port names is built in createMapForOneMeth (BackendNamingConventions).
// The method side numbers the ports with the multiplicity copy as the outer
// loop and the arguments inner; the Verilog side must do the same (matching the
// order AVerilogUtil emits).  A previous version expanded the multiplicity with
// the ports outer and the copy inner, which transposed the two lists and
// produced mismatched connections, e.g. ".A_2(someModule$A_3)" instead of
// ".A_2(someModule$A_2)".
//
// This checks that each Verilog port of the instantiated submodule connects to
// the matching internal wire (identity mapping).

package IncorrectPortMapping;

interface SomeInterface;
  method Action someMethod(bit a, bit b);
endinterface

import "BVI" SomeVerilogModule =
module mkSomeVerilogModule (SomeInterface);
  method someMethod[4](A, B) enable(ENABLE);

  schedule someMethod CF someMethod;
endmodule

(* synthesize *)
module mkExample ();
  SomeInterface someModule <- mkSomeVerilogModule();
endmodule

endpackage
