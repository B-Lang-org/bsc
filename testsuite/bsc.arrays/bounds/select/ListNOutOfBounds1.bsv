import ListN::*;

(* synthesize *)
module sysListNOutOfBounds1();
   List#(Integer) x = List::cons(1, 
                      List::cons(2, 
                      List::cons(3, 
                      List::cons(4, List::nil))));
   ListN#(4, Integer) ln = toListN(x);
   Integer y = ln[5];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule
