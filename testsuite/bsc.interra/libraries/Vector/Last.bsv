package Last;

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



module mkTestbench_Last();
   Vector #(5,Int #(4)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));



   rule fire_once (True);
      $display("Vector=");
      display_list (my_list1);
      $display("Last Element = %d", last(my_list1));
      if (last(my_list1) != 4 )
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule

endmodule : mkTestbench_Last
endpackage : Last
