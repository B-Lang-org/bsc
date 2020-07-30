package DeriveBits2;

// we use different identifiers everywhere to prevent from
// confusing two different things with the same name (in different scopes)
// in dump and debugging output

typedef union tagged {
   void Nilx;
   struct {
       dtype c1ar;
       Kens2List#(dtype) c1dr;
        } Cons1x;
} Kens1List#(type dtype)
deriving (Bits)
;

typedef union tagged {
   void Nily;
   struct {
       data2type c2ar;
       Kens1List#(data2type) c2dr;
        } Cons2y;
} Kens2List#(type data2type)
deriving(Bits)
;

(* synthesize *)
module sysDeriveBits2();
   rule foo;
    Kens1List#(int) a=Nilx;
    $display(a);

    $finish(0);
   endrule
     
endmodule

endpackage
