import List::*;
(* synthesize *)
module sysDynamicListDynamicUpdate(Empty);
   
   List#(int) l0 = cons (0, cons(1, cons (2, nil)));
   List#(int) l1 = cons (3, cons(4, cons (5, cons (6, nil)))); 
   
   Reg#(Bool) b <- mkReg(False);
   Reg#(Bit#(1)) i <- mkReg(0);

   let l = b ? l0 : l1;
   let l2 = l;
   l[i] = 3;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      $display("l[0]: %0d", l[0]);
      $display("l[1]: %0d", l[1]);
      $display("l[2]: %0d", l[2]);
      if (!b) $display("l[3]: %0d", l[3]);
      if (l == l) 
        $display("List is equal");
      else 
        $display ("List is NOT equal");
      if (l2 == l) 
        $display("l2 is equal");
      else
        $display("l2 is not equal");
      if(l2 == l1)
        $display("l2 equals l1");
      else
        $display("l2 does not equal l1");
   endrule
   
   rule toggle;      
      if (b) $finish(0);
      b <= !b;
   endrule

endmodule
   
   
