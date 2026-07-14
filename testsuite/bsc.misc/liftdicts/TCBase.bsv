package TCBase;

// The typeclass and its general instance.  The evidence-divergence
// tests build on this: an importing package can add a more specific
// (orphan) instance, and packages then legitimately disagree about
// the evidence for TC#(Maybe#(Bool)).

typeclass TC#(type t);
   function Bit#(8) tag(t x);
endtypeclass

instance TC#(Maybe#(t));
   function tag(x) = 8'd1;
endinstance

endpackage
