import List::*;
(* synthesize *)
module sysDynamicListDynamicActionDynamicIndex(Empty);
   
   List#(Action) l0 = cons($display(0),
                        cons($display(1),
                          cons($display(2), nil)));
   List#(Action) l1 = cons($display(3), 
                        cons($display(4),
                          cons($display(5),
                            cons($display(6), nil))));
   
   Reg#(Bool) b <- mkReg(False);
   Reg#(Bit#(2)) i <- mkReg(0);

   let l = b ? l0 : l1;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      l[i];
      b <= !b;
      if (b) begin 
        i <= i + 1;
        if (i == 3) $finish(0);
      end 
   endrule

endmodule
   
   
