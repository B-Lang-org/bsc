// A module whose interface has an always_enabled method.  Such a module
// cannot be the top of a normal Bluesim simulation (it is rejected with
// G0062), but -block-codegen must accept it as a codegen root, since the
// generated model is never executed.
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

endpackage
