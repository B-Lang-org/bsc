package T1Top;
import TCBase::*;
import TCMid::*;

// A more specific orphan instance (T0127 warns).  This package's
// resolution of TC#(Maybe#(Bool)) picks it; TCMid's dictionary was
// built from the general instance.  The two dictionaries have the
// same type but DIFFERENT evidence: neither may replace the other.
instance TC#(Maybe#(Bool));
   function tag(x) = 8'd2;
endinstance

function Bit#(8) topTag(Maybe#(Bool) x) = tag(x);

(* synthesize *)
module sysT1Top(Empty);
   rule r;
      let v = tagged Valid True;
      $display("mid=%0d top=%0d", midTag(v), topTag(v));
      $finish(0);
   endrule
endmodule

endpackage
