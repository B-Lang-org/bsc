package Sequence;

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
      return (a + b);
	endactionvalue
endfunction

module mkTestbench_Sequence();
   ListN #(5,Int #(32)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, nil)))));
   ListN #(3,ActionValue#(Int#(32))) my_list2 = 
                                 cons  (actionvalue 
                                          Int#(32) x = 5 ; return(x) ; 
									   endactionvalue, 
                                 cons (actionvalue 
                                          Int#(32) x = 6 ; return(x) ; 
									   endactionvalue, 
								 cons (actionvalue
                                          Int#(32) x = 7 ; return(x) ; 
									   endactionvalue,nil)));

   ListN #(3,Int #(32)) my_list4 = cons (5, cons (6, cons (7, nil)));



  
   rule fire_once (True);

      ListN #(3,Int #(32)) my_list3 <- sequence(my_list2);

      if (my_list4 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Sequence
endpackage : Sequence
