package Foldl;

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

function Int #(5) add (Int #(5) b, Integer a);
    return (fromInteger (a) + b);
endfunction

module mkTestbench_Foldl();
   Vector #(5,Integer) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));


  
   rule fire_once (True);
      $display("Sum of list of first five integers = %d", foldl (add, 0, my_list1));
      if (foldl(add, 0, my_list1) != 15) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Foldl
endpackage : Foldl
