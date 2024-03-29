package FoldM;

import ListN :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (ListN #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function ActionValue#(Int #(32)) add (Int #(32) a, Int #(32) b);
	actionvalue
	  noAction;
      return (a+b);
	endactionvalue
endfunction

module mkTestbench_FoldM();
   ListN #(5,Int #(32)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));




   rule fire_once (True);
      Int #(32) value <- foldM(add,my_list1);
      $display("%d", value);
      if (value != 15)
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule

endmodule : mkTestbench_FoldM
endpackage : FoldM
