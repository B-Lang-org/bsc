package Rotate;

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



module mkTestbench_Rotate();
   ListN #(5,Int #(32)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));
   ListN #(5,Int #(32)) my_list2 = cons (2, cons (3, cons (4, cons (5, cons (1, nil)))));



   rule fire_once (True);
      $display("Original ListN");
      display_list (my_list1);
      $display("Rotated ListN");
      display_list (rotate (my_list1));

      if (my_list2 != rotate(my_list1))
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule

endmodule : mkTestbench_Rotate
endpackage : Rotate
