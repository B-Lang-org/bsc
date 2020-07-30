package ReplicateM;

import Vector :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (Vector #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction


function ActionValue#(Int #(32)) add (Int #(32) a, Int #(32) b);
	actionvalue
	  noAction;
      return (a + b);
	endactionvalue
endfunction


module mkTestbench_ReplicateM();
   Vector #(5,Int #(32)) my_list1 = cons (1, cons (1, cons (1, cons (1, cons (1, nil)))));
   Vector #(5,Int #(32)) my_list3 = cons (10, cons (10, cons (10, cons (10, cons (10, nil)))));



  
   rule fire_once (True);
      Vector #(5,Int #(32)) my_list2 <- replicateM (foldlM(add,5,my_list1));
      $display("Vector of five 1's");
      display_list (my_list2);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ReplicateM
endpackage : ReplicateM
