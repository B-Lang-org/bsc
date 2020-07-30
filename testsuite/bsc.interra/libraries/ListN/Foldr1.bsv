package Foldr1;

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

function Int #(5) add (Int #(5) a, Int #(5) b);
    return (a + b);
endfunction

module mkTestbench_Foldr1();
   ListN #(5,Int #(5)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));


  
   rule fire_once (True);
      $display("Sum of list of first five integers = %d", foldr1 (add, my_list1));
      if (foldr1(add,my_list1) != 15) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Foldr1
endpackage : Foldr1
