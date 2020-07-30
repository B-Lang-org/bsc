package Replicate;

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



module mkTestbench_Replicate();
   Vector #(5,Int #(32)) my_list1 = cons (1, cons (1, cons (1, cons (1, cons (1, nil)))));
   Vector #(5,Int #(32)) my_list2 = replicate (1);



  
   rule fire_once (True);
      $display("Vector of five 1's");
      display_list (my_list2);
      if (my_list2 != my_list1) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Replicate
endpackage : Replicate
