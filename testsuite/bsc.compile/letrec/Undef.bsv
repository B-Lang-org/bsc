package Undef;

// we use different identifiers everywhere to prevent from
// confusing two different things with the same name (in different scopes)
// in dump and debugging output

typedef struct {
       dtype car;
       Kens1List#(dtype) cdr;
} Kens1List#(type dtype)
;

(* synthesize *)
module sysUndef();
   rule foo;
    Kens1List#(int) a;
    a.car=123;
    $display(a.car);

    $finish(0);
   endrule
     
endmodule

endpackage
