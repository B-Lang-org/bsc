package ToList;

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



module mkTestbench_ToList();
   Vector #(5,Int #(4)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   List #(Int #(4)) my_list2 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));

   List #(Int #(4)) my_list3 = toList(my_list1);


   rule fire_once (True);
      if (my_list3 != my_list2) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ToList
endpackage : ToList
