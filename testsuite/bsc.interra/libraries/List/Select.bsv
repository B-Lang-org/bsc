package Select;

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



module mkTestbench_Select();
   List #(Int #(32)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));

   Integer index = 3;


  
   rule fire_once (True);
      $display("List");
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
