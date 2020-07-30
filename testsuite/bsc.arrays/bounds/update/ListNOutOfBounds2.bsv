import ListN::*;

(* synthesize *)
module sysListNOutOfBounds2();
   List#(Integer) x = List::cons(1, 
                      List::cons(2, 
                      List::cons(3, 
                      List::cons(4, List::nil))));
   ListN#(4, Integer) ln = toListN(x);
   ln[-1] = 17;

   rule test;
      for(Integer i = 0; i < 4; i = i + 1)
      begin
	 $display("%0d", ln[i]);
      end
      $finish(0);
   endrule
  
endmodule
