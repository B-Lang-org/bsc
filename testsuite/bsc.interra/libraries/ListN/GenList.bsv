package GenList;

import ListN :: *;

module mkTestbench_GenList();
   ListN #(5,Integer) my_list1 = cons (0, cons (1, cons (2, cons (3,cons (4,nil)))));
   ListN #(5,Integer) my_list2 = genList;


   rule fire_once (True);
      if (my_list1 != my_list2) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_GenList
endpackage : GenList
