// Concats four Lists and checks against the expected list
package Concat;

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



module mkTestbench_Concat();
   List #(Int #(32)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Int #(32)) my_list2 = Cons (5, Cons (6, Cons (7, Cons (8, Cons (9, Nil)))));
   List #(Int #(32)) my_list3 = Cons (10, Cons (11, Cons (12, Cons (13, Cons (14, Nil)))));
   List #(Int #(32)) my_list4 = Cons (15, Cons (16, Cons (17, Cons (18, Cons (19, Nil)))));

   List #(List #(Int #(32))) my_list5 = Cons (my_list1, Cons (my_list2, Cons (my_list3, Cons (my_list4, Nil))));

   List #(Int #(32)) my_list6 = Cons(0, Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Cons (7, Cons (8, Cons (9, Cons (10, Cons (11, Cons (12, Cons (13, Cons(14, Cons (15, Cons (16, Cons (17, Cons (18, Cons (19, Nil))))))))))))))))))));


   rule fire_once (True);
      $display ("Concatenated List:");
      display_list (concat(my_list5));
      if (concat(my_list5) != my_list6) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Concat
endpackage : Concat
