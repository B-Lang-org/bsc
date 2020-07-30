(* synthesize *)
module sysListOutOfBounds2();
   List#(Integer) x = cons(1, cons(2, cons(3, cons(4, nil))));
   x[-1] = 17;

   rule test;
      for(Integer i = 0; i < 4; i = i + 1)
      begin
	 $display("%0d", x[i]);
      end
      $finish(0);
   endrule

endmodule
