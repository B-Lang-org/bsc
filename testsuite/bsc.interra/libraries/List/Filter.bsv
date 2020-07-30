//Shows how to use filter to remove negative elements from a List

package Filter;

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

function Bool f (Int #(8) a);
     if (a < 0)
        return False;
     else
        return True;
endfunction


module mkTestbench_Filter();
   List #(Int #(8)) my_list1 = Cons (0, Cons (-1, Cons (2, Cons (-3, Cons (4, Nil)))));
   List #(Int #(8)) my_list2 = filter (f, my_list1);
   List #(Int #(8)) my_list3 = Cons (0, Cons (2, Cons (4, Nil)));



   rule fire_once (True);
      $display ("Original List:");
      display_list (my_list1);
      $display ("Non-negative List:");
      display_list (my_list2);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Filter
endpackage : Filter
