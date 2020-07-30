package Update;

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



module mkTestbench_Update();
   List #(Int #(32)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(Int #(32)) my_list2 = Cons (1, Cons (2, Cons (3, Cons (6, Cons (5, Nil)))));

   Integer index = 3;
   List #(Int #(32)) my_list3 = update(my_list1, index, 6);


  
   rule fire_once (True);
      $display("Original List");
      display_list (my_list1);
      $display("Updated List");
      display_list (my_list3);
      
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Update
endpackage : Update
