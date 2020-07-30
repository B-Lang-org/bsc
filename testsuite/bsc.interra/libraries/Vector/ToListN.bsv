package ToListN;

import Vector :: *;

module mkTestbench_ToListN();

   Vector #(5,Int #(4)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   List #(Int #(4)) my_list2 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));

   Vector #(5,Int #(4)) my_list3 = toVector(my_list2);


   rule fire_once (True);
      if (my_list3 != my_list1) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ToListN
endpackage : ToListN
