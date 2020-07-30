(* synthesize *)
module sysListOutOfBounds1();
   List#(Integer) x = cons(1, cons(2, cons(3, cons(4, nil))));
   Integer y = x[5];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule
