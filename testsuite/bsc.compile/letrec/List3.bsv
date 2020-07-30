package List3;

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
;

instance Eq#(Kens1List#(a)) provisos (Eq#(a), Eq#(Kens1List#(a))) ;
  function Bool \== (Kens1List#(a) x, Kens1List#(a) y);
    case (x) matches
    tagged Nilx : case (y) matches
              tagged Nilx : return True;
              default : return False ;
              endcase
    tagged Cons1x { c1ar : .hdx, c1dr : .tlx } : case (y) matches
              tagged Cons1x { c1ar : .hdy, c1dr : .tly } : return ( hdx == hdy) && (tlx == tly);
              default : return False ;
              endcase
    endcase
  endfunction
endinstance

typedef union tagged {
   void Nily;
   struct {
       data2type c2ar;
       Kens3List#(data2type) c2dr;
        } Cons2y;
} Kens2List#(type data2type)
;


instance Eq#(Kens2List#(bb)) provisos (Eq#(bb),Eq#(Kens3List#(bb))) ;
  function Bool \== (Kens2List#(bb) x, Kens2List#(bb) y);
    case (x) matches
    tagged Nily : case (y) matches
              tagged Nily : return True;
              default : return False ;
              endcase
    tagged Cons2y { c2ar : .hdx, c2dr : .tlx } : case (y) matches
              tagged Cons2y { c2ar : .hdy, c2dr : .tly } : return ( hdx == hdy)  && (tlx == tly);
              default : return False ;
              endcase
    endcase
  endfunction
endinstance


typedef union tagged {
   void Nilz;
   struct {
       data3type c3ar;
       Kens1List#(data3type) c3dr;
        } Cons3z;
} Kens3List#(type data3type)
//deriving (Eq)
;

instance Eq#(Kens3List#(ccc)) provisos (Eq#(ccc),Eq#(Kens1List#(ccc))) ;
  function Bool \== (Kens3List#(ccc) x, Kens3List#(ccc) y);
    case (x) matches
    tagged Nilz : case (y) matches
              tagged Nilz : return True;
              default : return False ;
              endcase
    tagged Cons3z { c3ar : .hdx, c3dr : .tlx } : case (y) matches
              tagged Cons3z { c3ar : .hdy, c3dr : .tly } : return ( hdx == hdy)  && (tlx == tly);
              default : return False ;
              endcase
    endcase
  endfunction
endinstance

(* synthesize *)
module sysList3();
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
