import ListN::*;

(* synthesize *)
module sysListNInBounds2();
   List#(Integer) x = List::cons(1, 
                      List::cons(2, 
                      List::cons(3, 
                      List::cons(4, List::nil))));
   ListN#(4, Integer) ln = toListN(x);
   Bit#(1) ix = -1;
   Integer y = ln[ix];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule
