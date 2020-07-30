//Creates a List of five integers (1 to 5)
package Upto;

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



module mkTestbench_Upto();
   List #(Integer) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(Integer) my_list2 = upto (1, 5);
 
   List #(Int #(32)) my_list_3 = map (fromInteger, my_list1);


  
   rule fire_once (True);
      $display("List of first five integers");
      display_list (my_list_3);
      if (my_list2 != my_list1) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Upto
endpackage : Upto
