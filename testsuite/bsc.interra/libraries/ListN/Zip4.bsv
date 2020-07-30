package Zip4;

import ListN :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction

function Action displayabc1 (Tuple4#(a,a,a,a) abc) provisos (Bits #(a, sa));
    action
      $display ("%d", tpl_1(abc));
      $display ("%d", tpl_2(abc));
      $display ("%d", tpl_3(abc));
      $display ("%d", tpl_4(abc));
    endaction
endfunction


function Action display_list (ListN #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Action display_list1 (ListN #(n,Tuple4#(a,a,a,a)) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc1, my_list));
     endaction
endfunction



module mkTestbench_Zip4();
   ListN #(5,Int #(6)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Int #(6)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   ListN #(5,Int #(6)) my_list3 = cons (10, cons (11, cons (12, cons (13, cons (14, nil)))));
   ListN #(5,Int #(6)) my_list4 = cons (15, cons (16, cons (17, cons (18, cons (19, nil)))));
   ListN #(5,Tuple4#(Int #(6),Int #(6),Int #(6),Int #(6))) my_list5 = 
           cons (tuple4 (0,5,10,15), 
           cons (tuple4 (1,6,11,16), 
           cons (tuple4 (2,7,12,17), 
           cons (tuple4 (3,8,13,18), 
           cons (tuple4 (4,9,14,19), nil)))));


   rule fire_once (True);
      $display("ListN1:");
      display_list (my_list1);
      $display("ListN2:");
      display_list (my_list2);
      $display("ListN3:");
      display_list (my_list3);
      $display("ListN4:");
      display_list (my_list4);
      $display("Zipped ListN:");
      display_list1 (zip4(my_list1, my_list2,my_list3,my_list4));
      if (my_list5 != zip4 (my_list1, my_list2,my_list3,my_list4)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Zip4
endpackage : Zip4
