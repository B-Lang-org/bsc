package Equality;

import ListN :: *;

module mkTestbench_Equality();
   ListN #(5,Integer) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Integer) my_list2 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Integer) my_list3 = cons (1, cons (1, cons (2, cons (3, cons (4, nil)))));


   rule fire_once (True);
      if ((my_list1 == my_list2) && (my_list1 != my_list3))
        $display ("Simulation Passes");
      else
        $display ("Simulation Fails");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Equality

endpackage : Equality
