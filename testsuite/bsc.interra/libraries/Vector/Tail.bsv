package Tail;

import Vector :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (Vector #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction



module mkTestbench_Tail();
   Vector #(5,Int #(32)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
  
   Vector #(4,Int #(32)) my_list2 = tail (my_list1);
   Vector #(0,Int #(32)) my_list3 = tail(tail(tail(tail (tail (my_list1)))));
   


   rule fire_once (True);
      display_list (my_list1);
      display_list (my_list2);
      display_list (my_list3);
      if (head(my_list1) !=0 || head(my_list2) !=1 || my_list3 != nil ) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Tail
endpackage : Tail
