package GenWithM;

import ListN :: *;

function ActionValue#(Integer) f (Integer a);

	actionvalue
      noAction;
	  return(a+5);
	endactionvalue
endfunction

module mkTestbench_GenWithM();
   ListN #(5,Integer) my_list1 = cons (5, cons (6, cons (7, cons (8,cons (9,nil)))));


   rule fire_once (True);
      ListN #(5,Integer) my_list2 <- genWithM(f);
      if (my_list1 != my_list2) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_GenWithM
endpackage : GenWithM
