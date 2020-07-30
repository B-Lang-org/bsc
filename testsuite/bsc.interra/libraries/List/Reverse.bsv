package Reverse;

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



module mkTestbench_Reverse();
   List #(Int #(32)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Int #(32)) my_list2 = Cons (4, Cons (3, Cons (2, Cons (1, Cons (0, Nil)))));
   List #(Int #(32)) my_list3 = Nil;



   rule fire_once (True);
      $display ("Original List:");
      display_list (my_list1);
      $display ("Reversed List:");
      display_list (reverse(my_list1));

      if (reverse(my_list1) != my_list2 || reverse (my_list3) != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Reverse
endpackage : Reverse
