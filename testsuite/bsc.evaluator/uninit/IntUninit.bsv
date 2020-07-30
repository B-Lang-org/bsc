import ListN::*;

// double-check that ListN works
// and make sure we don't see the bit vector inside Int
(* synthesize *)
module mkListNIntUninitErr();
   ListN#(3,Int#(32)) x; 
   x[0] = 0;
   
   rule test;
      $display(x[1]);
      $finish(0);
   endrule
   
endmodule
