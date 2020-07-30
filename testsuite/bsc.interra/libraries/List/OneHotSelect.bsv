package OneHotSelect;

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



module mkTestbench_OneHotSelect();
   List #(UInt #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   
   List #(Bool) my_list2 = Cons (False, Cons (False, Cons (False, Cons (True, Cons (False, Cons (False, Cons (False, Cons (False, Cons (False, Cons (False, Nil))))))))));

  
   rule fire_once (True);
      $display("List1 (of unsigned integers):");
      display_list (my_list1);
      $display("List2 (of Booleans):");
      display_list (my_list2);
      $display("Returned Element= %b", oneHotSelect (my_list2, my_list1));
      if ( oneHotSelect (my_list2, my_list1) != 4) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_OneHotSelect




endpackage : OneHotSelect
