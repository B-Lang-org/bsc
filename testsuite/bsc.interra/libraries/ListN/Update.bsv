package Update;

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



module mkTestbench_Update();
   ListN #(5,Int #(32)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));
   ListN #(5,Int #(32)) my_list2 = cons (1, cons (2, cons (3, cons (6, cons (5, nil)))));

   Integer index = 3;
   ListN #(5,Int #(32)) my_list3 = update(my_list1, index, 6);


  
   rule fire_once (True);
      $display("Original ListN");
      display_list (my_list1);
      $display("Updated ListN");
      display_list (my_list3);
      
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Update
endpackage : Update
