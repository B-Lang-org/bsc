package Undef2;

// we use different identifiers everywhere to prevent from
// confusing two different things with the same name (in different scopes)
// in dump and debugging output

typedef struct {
       dtype car;
       Kens1List#(dtype) cdr;
} Kens1List#(type dtype)
deriving(Eq)
;

(* synthesize *)
module sysUndef2();
   rule foo;
    Kens1List#(int) a;
    a.cdr= ? ;
    $display(a.cdr==a.cdr);

    $finish(0);
   endrule
     
endmodule

endpackage
