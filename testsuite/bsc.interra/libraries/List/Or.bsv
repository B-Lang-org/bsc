package Or;

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



module mkTestbench_Or();
   List #(Bool) my_list1 = Cons (False, Cons (False, Cons (False, Cons (False, Cons (False, Nil)))));
   List #(Bool) my_list2 = Cons (False, Cons (False, Cons (True, Cons (False, Cons (False, Nil)))));


   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("Ored Value = %d", or (my_list1));
      $display("List2:");
      display_list (my_list2);
      $display("Ored Value = %d", or (my_list2));
      
      if (or(my_list1) != False || or (my_list2) != True) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Or
endpackage : Or
