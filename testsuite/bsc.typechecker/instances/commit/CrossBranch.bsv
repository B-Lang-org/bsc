package CrossBranch;

// A3, cross-branch enumeration: candidates live in different trie
// branches (Bool, Bit#(4), and the catch-all under Nothing).  The
// first use matches only the catch-all, reached by descending the
// Nothing branch alongside concrete branches; the second compiles
// only if the specific clause is walked BEFORE the catch-all (the
// catch-all's output a = Bool would conflict with the demanded
// Bit#(8) and, walked first, would be a final conflict).

typeclass D#(type a, type b) dependencies (a determines b);
  function b dd(a x);
endtypeclass

instance D#(Bool, Bit#(8));
  function dd(x) = 1;
endinstance

instance D#(Bit#(4), Bit#(16));
  function dd(x) = 2;
endinstance

instance D#(a, a);
  function dd(x) = x;
endinstance

(* synthesize *)
module mkCrossBranch();
  rule r;
    UInt#(3) u = 5;
    UInt#(3) w = dd(u);
    Bit#(8) y = dd(True);
    $display(w, y);
  endrule
endmodule
endpackage
