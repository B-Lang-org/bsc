package GivenBlocksCommit;

// A4: a unifiable given blocks commitment.  The catch-all instance
// MATCHES the inner wanted Sober#(t) with an unresolvable subgoal
// (Bits#(t, st) for opaque t); committing would strand that subgoal.
// The gate defers the pred whole, it rides to the outer definition,
// and the given discharges it.

typeclass Sober#(type t);
  function Bit#(8) sober(t x);
endtypeclass

instance Sober#(a) provisos (Bits#(a, sa), Add#(sa, 1, sb));
  function sober(x) = 7;
endinstance

function Bit#(8) outer(t x) provisos (Sober#(t));
  function Bit#(8) innerF(t y);
    return sober(y);
  endfunction
  return innerF(x);
endfunction

(* synthesize *)
module mkGivenBlocksCommit();
  rule r;
    $display(outer(True));
  endrule
endmodule
endpackage
