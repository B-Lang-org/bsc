package ChainAncestry;

// A9: reporting stays anchored to the user-written predicate through
// a two-layer instance chain ending in an unsatisfiable obligation.

typeclass Layer1#(type a);
  function Bit#(8) l1(a x);
endtypeclass

typeclass Layer2#(type a);
  function Bit#(8) l2(a x);
endtypeclass

instance Layer2#(Bit#(n)) provisos (Add#(n, n, 9));
  function l2(x) = 1;
endinstance

instance Layer1#(a) provisos (Layer2#(a));
  function l1(x) = l2(x);
endinstance

(* synthesize *)
module mkChainAncestry();
  rule r;
    Bit#(4) v = 3;
    $display(l1(v));
  endrule
endmodule
endpackage
