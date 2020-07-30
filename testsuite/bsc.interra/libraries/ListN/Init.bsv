package Init;

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



module mkTestbench_Init();
   ListN #(5,Int #(4)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(4,Int #(4)) my_list2 = cons (0, cons (1, cons (2, cons (3, nil))));


   rule fire_once (True);
      $display("ListN:");
      display_list (my_list1);
      $display("Init (ListN):");
      display_list (init(my_list1));
      if (my_list2 != init (my_list1)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Init
endpackage : Init
