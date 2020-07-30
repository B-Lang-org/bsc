(* synthesize *)
module sysSimpleDynamicListAction(Empty);

   
   List#(Action) l0 = cons($display(0),
                        cons($display(1),
                          cons($display(2), nil)));
   List#(Action) l1 = cons($display(3), 
                        cons($display(4),
                          cons($display(5),
                            cons($display(6), nil))));
   
   Reg#(Bool) b <- mkReg(False);
   
   let l = b ? l0 : l1;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      $display("l[1]");
      l[1];
      let l2 = l;
      l2[2] = $display(7);
      $display("l2[2]");
      l2[2];
   endrule
   
   rule toggle;      
      if (b) $finish(0);
      b <= !b;
   endrule

endmodule
   
   
