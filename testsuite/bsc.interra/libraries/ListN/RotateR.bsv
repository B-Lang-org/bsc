package RotateR;

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



module mkTestbench_RotateR();
   ListN #(5,Int #(32)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));
   ListN #(5,Int #(32)) my_list2 = cons (5, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(0,Int #(32)) my_list3 = nil;

  
   rule fire_once (True);
      $display("Original ListN");
      display_list (my_list1);
      $display("RRotated ListN");
      display_list (rotateR (my_list1));
      
      if (my_list2 != rotateR(my_list1) || rotateR(my_list3) != nil) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_RotateR
endpackage : RotateR
