package List2;

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
       Kens1List#(data2type) c2dr;
        } Cons2y;
} Kens2List#(type data2type)
;


instance Eq#(Kens2List#(bb)) provisos (Eq#(bb),Eq#(Kens1List#(bb))) ;
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


(* synthesize *)
module sysList2();
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
