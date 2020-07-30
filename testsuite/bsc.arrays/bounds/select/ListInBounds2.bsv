(* synthesize *)
module sysListInBounds2();
   List#(Integer) x = cons(1, cons(2, cons(3, cons(4, nil))));
   Bit#(1) ix = -1;
   Integer y = x[ix];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule
