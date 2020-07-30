package Select;

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



module mkTestbench_Select();
   ListN #(5,Int #(32)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));

   Integer index = 3;


  
   rule fire_once (True);
      $display("ListN");
      display_list (my_list1);
      $display("Selected Element = %d", select (my_list1, index));
      
      if (select(my_list1, index) != 4) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Select
endpackage : Select
