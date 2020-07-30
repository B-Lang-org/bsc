package Drop;

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



module mkTestbench_Drop();
   List #(Int #(4)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(Int #(4)) my_list2 = Cons (4, Nil);



   rule fire_once (True);
      $display ("Original List:");
      display_list (my_list1);
      $display ("Dropping four elements. New List:");
      display_list (drop(4, my_list1));
      if (drop(4, my_list1) != my_list2 || drop (6, my_list1) != Nil) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Drop
endpackage : Drop
