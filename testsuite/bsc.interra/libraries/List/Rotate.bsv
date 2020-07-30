package Rotate;

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



module mkTestbench_Rotate();
   List #(Int #(32)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(Int #(32)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Cons (1, Nil)))));


  
   rule fire_once (True);
      $display("Original List");
      display_list (my_list1);
      $display("Rotated List");
      display_list (rotate (my_list1));
      
      if (my_list2 != rotate(my_list1)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Rotate
endpackage : Rotate
