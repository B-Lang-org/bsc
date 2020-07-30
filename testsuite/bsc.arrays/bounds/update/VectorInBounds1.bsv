import Vector::*;

(* synthesize *)
module sysVectorInBounds1();
   Integer x[4] = {1, 2, 3, 4};
   Vector#(4, Integer) v = arrayToVector(x);
   v[1] = 17;

   rule test;
      for(Integer i = 0; i < 4; i = i + 1)
      begin
	 $display("%0d", v[i]);
      end
      $finish(0);
   endrule

endmodule
