package Elem;

import List :: *;

module mkTestbench_Elem();
   List #(Int #(32)) my_list1 = Cons (0, Cons (-1, Cons (2, Cons (3, Cons (4, Nil)))));


   rule fire_once (True);
      if (elem(0, my_list1) !=True ||  elem(1, my_list1) !=False || elem(2, my_list1) !=True || elem(3, my_list1) !=True || elem(5, my_list1) !=False || elem(4, my_list1) !=True || elem(-1, my_list1) !=True || elem(0, my_list1) !=True || elem(6, my_list1) !=False)
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Elem
endpackage : Elem
