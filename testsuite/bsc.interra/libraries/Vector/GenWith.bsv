package GenWith;

import Vector :: *;

function Integer f (Integer a);

    Integer c = a + 5;
	return(c);
endfunction

module mkTestbench_GenWith();
   Vector #(5,Integer) my_list1 = cons (5, cons (6, cons (7, cons (8,cons (9,nil)))));
   Vector #(5,Integer) my_list2 = genWith(f);


   rule fire_once (True);
      if (my_list1 != my_list2) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_GenWith
endpackage : GenWith
