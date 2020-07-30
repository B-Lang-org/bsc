package ZipAny;

import Vector :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction

function Action displayabc1 (Tuple2#(a,a) abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc.fst);
      $display ("%d", abc.snd);
    endaction
endfunction


function Action display_list (Vector #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Action display_list1 (Vector #(n,Tuple2#(a,a)) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc1, my_list));
     endaction
endfunction



module mkTestbench_ZipAny(); // provisos (Max#(8,a,8), Max#(5,a,5));
   Vector #(5,Int #(5)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   Vector #(8,Int #(5)) my_list2 = 
                       cons (5, 
					   cons (6, 
					   cons (7, 
					   cons (8, 
					   cons (9, 
					   cons (10, 
					   cons (11, 
					   cons (12, nil))))))));

   Vector #(5,Tuple2#(Int #(5),Int #(5))) my_list3 = 
           cons (tuple2 (0,5), 
           cons (tuple2 (1,6), 
           cons (tuple2 (2,7), 
           cons (tuple2 (3,8), 
           cons (tuple2 (4,9), nil)))));
   Vector #(5,Tuple2#(Int #(5),Int #(5))) my_list4 = zipAny(my_list1, my_list2);


   rule fire_once (True);
      $display("ListN1:");
      display_list (my_list1);
      $display("ListN2:");
      display_list (my_list2);
      $display("ZipAnyped Vector:");
      display_list1 (my_list4);
      if (my_list3 != my_list4) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipAny
endpackage : ZipAny
