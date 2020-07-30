package Length;

import List :: *;




module mkTestbench_Length();
   List #(Int #(4)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Int #(4)) my_list2 = Nil;


   rule fire_once (True);
      if (length(my_list1) != 5 || length (my_list2) != 0) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Length
endpackage : Length
