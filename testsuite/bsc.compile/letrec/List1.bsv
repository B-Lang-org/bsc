package List1;

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


(* synthesize *)
module sysList1();
   rule foo;
    Kens1List#(int) a=Nilx;
    Kens1List#(int) b=Nilx;
    Kens1List#(int) c=tagged Cons1x { c1ar:10, c1dr: Nilx};
    Kens1List#(int) d=tagged Cons1x { c1ar:10, c1dr: Nilx};
    Kens1List#(int) e=tagged Cons1x { c1ar:20, c1dr: Nilx};
    $display(a==b);
    $display(a==c);
    $display(c==d);
    $display(c==e);

    $finish(0);
   endrule
     
endmodule

endpackage
