package JoinActions;

import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("Simulation Passes");
    endaction
endfunction



module mkTestbench_JoinActions();
   List #(Int #(32)) my_list = Cons (0, Nil);

   rule fire_once (True);
      joinActions (map (displayabc, my_list));
      $finish (2'b00);
   endrule 
      
endmodule : mkTestbench_JoinActions
endpackage : JoinActions
