package Take;

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



module mkTestbench_Take();
   ListN #(5,Int #(4)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(2,Int #(4)) my_list2 = cons (0, cons(1, nil));
   ListN #(2,Int #(4)) my_list3 = take (my_list1);



   rule fire_once (True);
      $display ("Original ListN:");
      display_list (my_list1);
      $display ("Taking two elements. New ListN:");
      display_list (my_list3);
      if (my_list3 != my_list2 )
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Take
endpackage : Take
