import List::*;
(* synthesize *)
module sysSimpleDynamicList(Empty);
   
   List#(int) l0 = cons (0, cons(1, cons (2, nil)));
   List#(int) l1 = cons (3, cons(4, cons (5, cons (6, nil)))); 
   
   Reg#(Bool) b <- mkReg(False);
   
   let l = b ? l0 : l1;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      $display("l[1]: %0d", l[1]);
      if (l == l) 
        $display("List is equal");
      else 
        $display ("List is NOT equal");
      let l2 = l;
      l2[2] = 17;
      $display("l2[2] = %0d", l2[2]);
      if(l == l2)
        $display("l2 is EQUAL");
      else
        $display("l2 is not equal"); 
   endrule
   
   rule toggle;      
      if (b) $finish(0);
      b <= !b;
   endrule

endmodule
   
   
