package Zip3;

import Vector :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction

function Action displayabc1 (Tuple3#(a,a,a) abc) provisos (Bits #(a, sa));
    action
      $display ("%d", tpl_1(abc));
      $display ("%d", tpl_2(abc));
      $display ("%d", tpl_3(abc));
    endaction
endfunction


function Action display_list (Vector #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Action display_list1 (Vector #(n,Tuple3#(a,a,a)) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc1, my_list));
     endaction
endfunction



module mkTestbench_Zip3();
   Vector #(5,Int #(5)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   Vector #(5,Int #(5)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   Vector #(5,Int #(5)) my_list3 = cons (10, cons (11, cons (12, cons (13, cons (14, nil)))));
   Vector #(5,Tuple3#(Int #(5),Int #(5),Int #(5))) my_list4 = 
           cons (tuple3 (0,5,10), 
           cons (tuple3 (1,6,11), 
           cons (tuple3 (2,7,12), 
           cons (tuple3 (3,8,13), 
           cons (tuple3 (4,9,14), nil)))));


   rule fire_once (True);
      $display("ListN1:");
      display_list (my_list1);
      $display("ListN2:");
      display_list (my_list2);
      $display("ListN3:");
      display_list (my_list3);
      $display("Zipped Vector:");
      display_list1 (zip3(my_list1, my_list2,my_list3));
      if (my_list4 != zip3 (my_list1, my_list2,my_list3)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Zip3
endpackage : Zip3
