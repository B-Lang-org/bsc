package Test ;


(* synthesize *)
module mkFoo(Empty);
  Reg#(Int#(32)) x();
  mkRegU the_x(x);

  rule zero (x == 0);
    x <= x+1;
  endrule

  rule grter_four (x > 4) ;
    x <= x-1;
  endrule

  rule non_zero ((x > 0) && ((x-1) < 3)) ;
    x <= x-1;
  endrule

endmodule // mkFoo

endpackage
