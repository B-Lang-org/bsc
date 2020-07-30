package All;

import ListN :: *;
function Bool f (Int #(32) a);
     if (a < 0)
        return False;
     else
        return True;
endfunction


module mkTestbench_All();
   ListN #(5,Int #(32)) my_list1 = cons (4, cons (-3, cons (-2, cons (1,cons (0,nil)))));
   ListN #(5,Int #(32)) my_list2 = cons (4, cons (3, cons (2, cons (1,cons (0,nil)))));



   rule fire_once (True);
      if (all(f, my_list1) != False || any(f, my_list2) != True) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_All
endpackage : All
