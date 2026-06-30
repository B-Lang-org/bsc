// A module whose interface has an always_enabled method.  Such a module
// cannot be the top of a normal Bluesim simulation (it is rejected with
// G0062), but -block-codegen must accept it as a codegen root, since the
// generated model is never executed.  mkUsesEnabled instantiates it so the
// testsuite can check that the block-codegen output matches the submodule
// form for this (motivating) case too.
package Enabled;

interface AlwaysEnabled;
  (* always_enabled *) method Action poke(Bit#(8) x);
  method Bit#(8) get();
endinterface

(* synthesize *)
module mkAlwaysEnabled(AlwaysEnabled);
  Reg#(Bit#(8)) r <- mkReg(0);
  method Action poke(Bit#(8) x); r <= x; endmethod
  method Bit#(8) get(); return r; endmethod
endmodule

(* synthesize *)
module mkUsesEnabled();
  AlwaysEnabled ae <- mkAlwaysEnabled;
  Reg#(Bit#(8)) n <- mkReg(0);
  rule drive;
    ae.poke(n);
    n <= n + 1;
    if (n == 5) begin $display("ae=%0d", ae.get()); $finish(0); end
  endrule
endmodule

endpackage
