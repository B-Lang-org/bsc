import List::*;
(* synthesize *)
module sysSimpleDynamicListBounds(Empty);
   
   List#(int) l0 = cons (0, cons(1, cons (2, nil)));
   List#(int) l1 = cons (3, cons(4, cons (5, cons (6, nil)))); 
   
   Reg#(Bool) b <- mkReg(False);
   
   let l = b ? l0 : l1;
   
   rule print;
      $display(l[4]);
      $finish(0);
   endrule
   
endmodule
   
   
