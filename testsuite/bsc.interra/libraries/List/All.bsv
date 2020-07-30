package All;

import List :: *;
function Bool f (Int #(32) a);
     if (a < 0)
        return False;
     else
        return True;
endfunction


module mkTestbench_All();
   List #(Int #(32)) my_list1 = Cons (0, Cons (-1, Cons (2, Cons (-3, Cons (4, Nil)))));
   List #(Int #(32)) my_list2 = Cons (0, Cons (2, Cons (4, Nil)));



   rule fire_once (True);
      if (all(f, my_list1) != False || all(f, my_list2) != True) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_All
endpackage : All
