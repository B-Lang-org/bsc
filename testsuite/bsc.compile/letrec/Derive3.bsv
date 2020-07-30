package Derive3;

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
deriving(Eq)
;

typedef union tagged {
   void Nily;
   struct {
       data2type c2ar;
       Kens3List#(data2type) c2dr;
        } Cons2y;
} Kens2List#(type data2type)
deriving(Eq)
;

typedef union tagged {
   void Nilz;
   struct {
       data3type c3ar;
       Kens1List#(data3type) c3dr;
        } Cons3z;
} Kens3List#(type data3type)
deriving (Eq)
;

(* synthesize *)
module sysDerive3();
   rule foo;
    Kens1List#(int) a=Nilx;
    Kens1List#(int) b=Nilx;
    Kens1List#(int) c=tagged Cons1x { c1ar:10, c1dr: Nily};
    Kens1List#(int) d=tagged Cons1x { c1ar:10, c1dr: Nily};
    Kens1List#(int) e=Cons1x{c1ar:10,c1dr:Cons2y{c2ar:20,c2dr:Cons3z{c3ar:30,c3dr:Cons1x{c1ar:40,c1dr:Nily}}}};
    Kens1List#(int) f=Cons1x{c1ar:10,c1dr:Cons2y{c2ar:20,c2dr:Cons3z{c3ar:30,c3dr:Cons1x{c1ar:40,c1dr:Nily}}}};
    Kens1List#(int) g=Cons1x{c1ar:10,c1dr:Cons2y{c2ar:20,c2dr:Cons3z{c3ar:30,c3dr:Cons1x{c1ar:41,c1dr:Nily}}}};
    $display(a==b);
    $display(a==c);
    $display(c==d);
    $display(c==e);
    $display(e==f);
    $display(e==g);

    $finish(0);
   endrule
     
endmodule

endpackage
