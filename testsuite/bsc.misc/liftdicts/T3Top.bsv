package T3Top;
import TCBase::*;
import TCMid::*;
import TCRight::*;

// Diamond: TCMid's dictionary was built from the general instance,
// TCRight's from its specific orphan instance.  This package sees the
// specific instance (via TCRight), so its own dictionary has TCRight's
// evidence: it must dedup against TCRight's dictionary (same
// fingerprint) while TCMid's (different fingerprint) stays intact.
function Bit#(8) topTag(Maybe#(Bool) x) = tag(x);

(* synthesize *)
module sysT3Top(Empty);
   rule r;
      let v = tagged Valid True;
      $display("mid=%0d right=%0d top=%0d", midTag(v), rightTag(v), topTag(v));
      $finish(0);
   endrule
endmodule

endpackage
