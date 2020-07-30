package Head;

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



module mkTestbench_Head();
   List #(Int #(32)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));


   rule fire_once (True);
      $display ("Head = %d", head(my_list1));
      if (head(my_list1) !=0) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Head
endpackage : Head
