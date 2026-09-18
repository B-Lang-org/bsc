// The BSV coherence annotation: a soft keyword between "typeclass" and
// the class name, mirroring Classic's "class incoherent".
//
// TwoLevel is declared incoherent, so it retains relational
// semantics: under (Bits#(a, na), Bits#(b, nb)) neither Bool-specific
// instance matches (a and b are not known to be Bool) and the
// catch-all is committed to (-> 1), without an incoherent-match
// warning (the annotation declares this is intended).

typeclass incoherent TwoLevel#(type a, type b);
   function Bit#(8) twoLevel(a x, b y);
endtypeclass

instance TwoLevel#(a, b);   // catch-all
   function twoLevel(x, y) = 1;
endinstance

instance TwoLevel#(Bool, b);
   function twoLevel(x, y) = 2;
endinstance

instance TwoLevel#(Bool, Bool);
   function twoLevel(x, y) = 3;
endinstance

function Bit#(8) throughBits(a x, b y)
   provisos (Bits#(a, na), Bits#(b, nb));
   return twoLevel(x, y);
endfunction

(* synthesize *)
module sysIncoherentKeywordBSV();
   rule test;
      $display("%0d", twoLevel(True, True));                  // 3
      $display("%0d", twoLevel(True, 8'd42));                 // 2
      $display("%0d", throughBits(True, True));               // 1 (incoherent)
      $finish(0);
   endrule
endmodule
