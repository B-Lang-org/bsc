package Init;

import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction



module mkTestbench_Init();
   List #(Int #(4)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Int #(4)) my_list2 = Cons (0, Cons (1, Cons (2, Cons (3, Nil))));


   rule fire_once (True);
      $display("List:");
      display_list (my_list1);
      $display("Init (List):");
      display_list (init(my_list1));
      if (my_list2 != init (my_list1)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Init
endpackage : Init
