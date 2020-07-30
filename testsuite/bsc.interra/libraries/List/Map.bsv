//This file shows how to use Map to get absolute value for each element in a list
package Map;

import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%b", abc);
    endaction
endfunction



function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction



module mkTestbench_Map();
   List #(Int #(8)) my_list1 = Cons (0, Cons (-1, Cons (-2, Cons (-3, Cons (-4, Nil)))));
   List #(Int #(8)) my_list2 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));

   List #(Int #(8)) my_list3 = map (negate, my_list1);

   rule fire_once (True);
      $display("Original List:");
      display_list(my_list1);
      $display("Negated List:");
      display_list(my_list3);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Map
endpackage : Map
