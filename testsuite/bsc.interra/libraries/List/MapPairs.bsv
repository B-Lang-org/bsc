package MapPairs;

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

function Bool f (Bit #(8) a, Bit #(8) b);
     if (a < b)
       return True;
     else
       return False;
endfunction

module mkTestbench_MapPairs();
   List #(Bit #(8)) my_list1 = Cons (0, Cons (1, Cons (6, Cons (3, Cons (4, Cons (9, Cons (1, Cons (7, Cons (3, Cons (2, Cons (9, Nil)))))))))));
   List #(Bool) my_list2 = Cons (True, Cons (False, Cons (True, Cons (True, Cons (False, Cons (True, Nil))))));

   List #(Bool) my_list3 = mapPairs (f, f(0), my_list1);

   rule fire_once (True);
      $display("Original List:");
      display_list(my_list1);
      $display("mapPaired List:");
      display_list(my_list3);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_MapPairs
endpackage : MapPairs
