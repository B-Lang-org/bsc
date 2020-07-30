package DeriveBits1;

// we use different identifiers everywhere to prevent from
// confusing two different things with the same name (in different scopes)
// in dump and debugging output

typedef union tagged {
   void Nilx;
   struct {
       dtype c1ar;
       Kens1List#(dtype) c1dr;
        } Cons1x;
} Kens1List#(type dtype)
deriving(Bits)
;

(* synthesize *)
module sysDeriveBits1();
   rule foo;
    Kens1List#(int) a=Nilx;
    // display will automatically call pack
    $display(a);
    $finish(0);
   endrule
     
endmodule

endpackage
