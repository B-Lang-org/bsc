package And;

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



module mkTestbench_And();
   List #(Bool) my_list1 = Cons (True, Cons (True, Cons (True, Cons (True, Cons (True, Nil)))));
   List #(Bool) my_list2 = Cons (False, Cons (False, Cons (True, Cons (False, Cons (False, Nil)))));


   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("And Value = %d", and (my_list1));
      $display("List2:");
      display_list (my_list2);
      $display("And Value = %d", and (my_list2));
      
      if (and(my_list1) != True || and (my_list2) != False) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_And
endpackage : And
