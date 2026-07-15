package T2Top;
import TCBase::*;
import TCMid::*;

// No orphan instance here: this package resolves TC#(Maybe#(Bool))
// with the same (general) evidence TCMid used, so its dictionary is
// deduplicated against TCMid's (see the trace assertion in the .exp).
function Bit#(8) topTag(Maybe#(Bool) x) = tag(x);

(* synthesize *)
module sysT2Top(Empty);
   rule r;
      let v = tagged Valid True;
      $display("mid=%0d top=%0d", midTag(v), topTag(v));
      $finish(0);
   endrule
endmodule

endpackage
