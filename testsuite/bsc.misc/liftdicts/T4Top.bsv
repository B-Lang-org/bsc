package T4Top;
import TCBase::*;
import TDBase::*;
import TDMid::*;

// The outer TD instance is the SAME as TDMid used; only the embedded
// TC sub-evidence differs (specific orphan here, general there).  A
// fingerprint that looked only at the root instance would wrongly
// dedup these; the recursive fingerprint must keep both.
instance TC#(Maybe#(Bool));
   function tag(x) = 8'd2;
endinstance

function Bit#(8) dtop(Maybe#(Bool) x) = dtag(x);

(* synthesize *)
module sysT4Top(Empty);
   rule r;
      let v = tagged Valid True;
      $display("dmid=%0d dtop=%0d", dmid(v), dtop(v));
      $finish(0);
   endrule
endmodule

endpackage
