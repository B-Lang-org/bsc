package Concat;

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



module mkTestbench_Concat();
   Vector #(5,Int #(32)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   Vector #(5,Int #(32)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   Vector #(5,Int #(32)) my_list3 = cons (10, cons (11, cons (12, cons (13, cons (14, nil)))));
   Vector #(5,Int #(32)) my_list4 = cons (15, cons (16, cons (17, cons (18, cons (19, nil)))));

   Vector #(4,Vector #(5,Int #(32))) my_list5 = cons (my_list1, cons (my_list2, cons (my_list3, cons (my_list4, nil))));

   Vector #(20,Int #(32)) my_list6 = cons(0, cons (1, cons (2, cons (3, cons (4, cons (5, cons (6, cons (7, cons (8, cons (9, cons (10, cons (11, cons (12, cons (13, cons(14, cons (15, cons (16, cons (17, cons (18, cons (19, nil))))))))))))))))))));


   rule fire_once (True);
      $display ("Concatenated Vector:");
      display_list (concat(my_list5));
      if (concat(my_list5) != my_list6) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Concat
endpackage : Concat
