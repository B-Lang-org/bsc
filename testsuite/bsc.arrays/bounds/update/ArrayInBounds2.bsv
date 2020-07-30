(* synthesize *)
module sysArrayInBounds2();
   Integer x[4] = {1, 2, 3, 4};
   Bit#(2) ix = -1;
   x[ix] = 17;

   rule test;
      for(Integer i = 0; i < 4; i = i + 1)
      begin
	 $display("%0d", x[i]);
      end
      $finish(0);
   endrule

endmodule
