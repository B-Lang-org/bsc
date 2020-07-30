package Tail;

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



module mkTestbench_Tail();
   List #(Int #(32)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
  
   List #(Int #(32)) my_list2 = tail (my_list1);
   List #(Int #(32)) my_list3 = tail(tail(tail(tail (tail (my_list1)))));
   


   rule fire_once (True);
      display_list (my_list1);
      display_list (my_list2);
      display_list (my_list3);
      if (head(my_list1) !=0 || length (my_list1) != 5 || head(my_list2) !=1 || length (my_list2) != 4 || my_list3 != Nil || length (my_list3) != 0) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Tail
endpackage : Tail
