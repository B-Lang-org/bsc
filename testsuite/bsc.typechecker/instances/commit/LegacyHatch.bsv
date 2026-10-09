package LegacyHatch;

// Ordered-clause commitment: the function-headed instance is the
// clause for function inputs; its determined output conflicting with
// the demanded type is a final error (T0159), not a license to fall
// through to the catch-all.  The legacy policy still falls through.

typeclass F#(type a, type b) dependencies (a determines b);
  function b ff(a x);
endtypeclass

instance F#(function Bool f(Bool x), Bit#(8));
  function ff(x) = 0;
endinstance

instance F#(a, b);
  function ff(x) = ?;
endinstance

function Bool notFn(Bool x) = !x;

(* synthesize *)
module mkLegacyHatch();
  rule r;
    Bool y = ff(notFn);
    $display(y);
  endrule
endmodule
endpackage
