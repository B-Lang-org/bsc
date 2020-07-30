//Creates a list of Int #(32) of size 5 and each element 1
package Replicate;

import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction



module mkTestbench_Replicate();
   List #(Int #(32)) my_list1 = Cons (1, Cons (1, Cons (1, Cons (1, Cons (1, Nil)))));
   List #(Int #(32)) my_list2 = replicate (5,1);



  
   rule fire_once (True);
      $display("List of five 1's");
      display_list (my_list2);
      if (my_list2 != my_list1) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Replicate
endpackage : Replicate
