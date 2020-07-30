package DeriveBits3;

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
deriving(Bits)
;

typedef union tagged {
   void Nily;
   struct {
       data2type c2ar;
       Kens3List#(data2type) c2dr;
        } Cons2y;
} Kens2List#(type data2type)
deriving(Bits)
;

typedef union tagged {
   void Nilz;
   struct {
       data3type c3ar;
       Kens1List#(data3type) c3dr;
        } Cons3z;
} Kens3List#(type data3type)
deriving (Bits)
;

(* synthesize *)
module sysDeriveBits3();
   rule foo;
    Kens1List#(int) a=Nilx;
    $display(a);
    $finish(0);
   endrule
     
endmodule

endpackage
