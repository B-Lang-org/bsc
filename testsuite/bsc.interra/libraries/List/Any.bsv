package Any;

import List :: *;
function Bool f (Int #(32) a);
     if (a < 0)
        return True;
     else
        return False;
endfunction


module mkTestbench_Any();
   List #(Int #(32)) my_list1 = Cons (0, Cons (-1, Cons (2, Cons (-3, Cons (4, Nil)))));
   List #(Int #(32)) my_list2 = Cons (0, Cons (2, Cons (4, Nil)));



   rule fire_once (True);
      if (any(f, my_list1) != True || any(f, my_list2) != False) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Any
endpackage : Any
