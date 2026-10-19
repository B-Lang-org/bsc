package IncoherentFallThrough;

// A5: the incoherent annotation licenses output-driven fall-through.
// The function-headed clause is selected by the input but its
// determined output conflicts with the demanded type; the marking
// (unlike the coherent LegacyHatch twin) permits falling through to
// the catch-all with no flag.

typeclass incoherent F#(type a, type b) dependencies (a determines b);
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
module mkIncoherentFallThrough();
  rule r;
    Bool y = ff(notFn);
    $display(y);
  endrule
endmodule
endpackage
