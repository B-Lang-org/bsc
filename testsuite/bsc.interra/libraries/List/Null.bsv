package Null;

import List :: *;


module mkTestbench_Null();
   List #(Int #(4)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Int #(4)) my_list2 = Nil;


   rule fire_once (True);
      if (null(my_list1) != False || null(my_list2) != True) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Null
endpackage : Null
