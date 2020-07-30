package Equality;

import List :: *;

module mkTestbench_Equality();
   List #(Integer) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Integer) my_list2 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Integer) my_list3 = Cons (1, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));


   rule fire_once (True);
      if ((my_list1 == my_list2) && (my_list1 != my_list3))
        $display ("Simulation Passes");
      else
        $display ("Simulation Fails");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Equality

endpackage : Equality
