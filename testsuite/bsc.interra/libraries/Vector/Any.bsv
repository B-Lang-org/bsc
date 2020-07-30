package Any;

import Vector :: *;
function Bool f (Int #(32) a);
     if (a < 0)
        return True;
     else
        return False;
endfunction


module mkTestbench_Any();
   Vector #(5,Int #(32)) my_list1 = cons (0, cons (-1, cons (2, cons (-3, cons (4, nil)))));
   Vector #(3,Int #(32)) my_list2 = cons (0, cons (2, cons (4, nil)));



   rule fire_once (True);
      if (any(f, my_list1) != True || any(f, my_list2) != False) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Any
endpackage : Any
