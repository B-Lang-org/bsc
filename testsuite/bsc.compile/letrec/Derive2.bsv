package Derive2;

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
deriving (Eq)
;

typedef union tagged {
   void Nily;
   struct {
       data2type c2ar;
       Kens1List#(data2type) c2dr;
        } Cons2y;
} Kens2List#(type data2type)
deriving(Eq)
;

(* synthesize *)
module sysDerive2();
   rule foo;
    Kens1List#(int) a=Nilx;
    Kens1List#(int) b=Nilx;
    Kens1List#(int) c=tagged Cons1x { c1ar:10, c1dr: Nily};
    Kens1List#(int) d=tagged Cons1x { c1ar:10, c1dr: Nily};
    Kens1List#(int) e=tagged Cons1x { c1ar:20, c1dr: Nily};
    $display(a==b);
    $display(a==c);
    $display(c==d);
    $display(c==e);

    $finish(0);
   endrule
     
endmodule

endpackage
