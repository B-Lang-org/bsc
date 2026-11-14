// The "coherent" annotation pins strict semantics even when the
// global -incoherent-instance-matches flag would allow an
// under-determined match: the polymorphic use in throughBits cannot
// commit to the catch-all, so the context is rejected.

package CoherentKeywordBSV;

typeclass coherent TwoLevel#(type a, type b);
   function Bit#(8) twoLevel(a x, b y);
endtypeclass

instance TwoLevel#(a, b);   // catch-all
   function twoLevel(x, y) = 1;
endinstance

instance TwoLevel#(Bool, Bool);
   function twoLevel(x, y) = 3;
endinstance

function Bit#(8) throughBits(a x, b y)
   provisos (Bits#(a, na), Bits#(b, nb));
   return twoLevel(x, y);
endfunction

endpackage
