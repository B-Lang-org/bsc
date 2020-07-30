package Reverse;

import ListN :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (ListN #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction



module mkTestbench_Reverse();
   ListN #(5,Int #(32)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Int #(32)) my_list2 = cons (4, cons (3, cons (2, cons (1, cons (0, nil)))));
   ListN #(0,Int #(32)) my_list3 = nil;



   rule fire_once (True);
      $display ("Original ListN:");
      display_list (my_list1);
      $display ("Reversed ListN:");
      display_list (reverse(my_list1));

      if (reverse(my_list1) != my_list2 || reverse (my_list3) != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Reverse
endpackage : Reverse
