package GivenIndependence;

// Pool given-independence: evidence derived from one definition's
// given must not be frozen and reused where the given is absent.
// useGiven discharges Sober#(t) from its proviso; useInstance must
// resolve the same class from the instance.

typeclass Sober#(type t);
  function Bit#(8) sober(t x);
endtypeclass

instance Sober#(Bool);
  function sober(x) = x ? 1 : 0;
endinstance

function Bit#(8) useGiven(t x) provisos (Sober#(t));
  return sober(x) + 1;
endfunction

function Bit#(8) useInstance(Bool x);
  return sober(x) + 2;
endfunction

(* synthesize *)
module mkGivenIndependence();
  rule r;
    $display(useGiven(True), useInstance(False));
  endrule
endmodule
endpackage
