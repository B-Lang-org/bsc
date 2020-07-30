package Transpose;

import List :: *;


module mkTestbench_Transpose();
   List #(Int #(32)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(List #(Int #(32))) my_list2 = replicate (10, my_list1);
   List #(List #(Int #(32))) my_list3 = transpose (my_list2);

   List #(List #(Int #(32))) my_list3_expected = Cons (replicate(10, 1), Cons (replicate(10, 2), Cons (replicate(10, 3), Cons (replicate(10, 4), Cons (replicate(10, 5), Nil))))); 
 

  
   rule fire_once (True);
      if (my_list3 != my_list3_expected) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
     
endmodule : mkTestbench_Transpose
endpackage : Transpose
