package Elem;

import Vector :: *;

module mkTestbench_Elem();
   Vector #(5,Int #(32)) my_list1 = cons (0, cons (-1, cons (2, cons (3, cons (4, nil)))));


   rule fire_once (True);
      if (elem(0, my_list1) !=True ||  elem(1, my_list1) !=False || elem(2, my_list1) !=True || elem(3, my_list1) !=True || elem(5, my_list1) !=False || elem(4, my_list1) !=True || elem(-1, my_list1) !=True || elem(0, my_list1) !=True || elem(6, my_list1) !=False)
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Elem
endpackage : Elem
