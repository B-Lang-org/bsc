// A leaf module that is reused, unchanged, in several different
// hierarchies.  It is a valid Bluesim top in its own right (no
// always_enabled methods, no top-level arguments), so the *same*
// module can be code-generated both with -block-codegen and via a
// normal -sim build, which the testsuite uses to check that the two
// paths emit byte-identical per-module C++.
package SharedSub;

interface Counter;
  method Action inc();
  method Bit#(8) value();
endinterface

(* synthesize *)
module mkSub(Counter);
  Reg#(Bit#(8)) r <- mkReg(0);
  method Action inc(); r <= r + 1; endmethod
  method Bit#(8) value(); return r; endmethod
endmodule

endpackage
