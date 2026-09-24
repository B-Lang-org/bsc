package Covered;

typeclass D#(type a, type b) dependencies (a determines b);
  function b g(a x);
endtypeclass

// st appears only in the determined position of the instance head; it
// is covered solely through the proviso's fundep (Bits#(t, st): t
// determines st), so this pins the proviso-closure half of the
// coverage check, not just direct coverage.
instance D#(t, Bit#(st)) provisos (Bits#(t, st));
  function g(x) = pack(x);
endinstance

(* synthesize *)
module mkCovered(); endmodule
endpackage
