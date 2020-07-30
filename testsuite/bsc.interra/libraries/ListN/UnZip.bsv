package UnZip;

import ListN :: *;

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


function Action display_list (ListN #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Action display_list1 (ListN #(n,Tuple2#(a,a)) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc1, my_list));
     endaction
endfunction



module mkTestbench_UnZip();
   ListN #(5,Int #(5)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Int #(5)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   ListN #(5,Tuple2#(Int #(5),Int #(5))) my_list3 = 
           cons (tuple2 (0,5), 
           cons (tuple2 (1,6), 
           cons (tuple2 (2,7), 
           cons (tuple2 (3,8), 
           cons (tuple2 (4,9), nil)))));
   Tuple2#(ListN #(5,Int #(5)),ListN #(5,Int #(5))) my_list4 = unzip(my_list3);
   ListN #(5,Int #(5)) my_list5 = tpl_1(my_list4);
   ListN #(5,Int #(5)) my_list6 = tpl_2(my_list4);

  


   rule fire_once (True);
      $display("Original ListN:");
      display_list (tpl_1(my_list4));
      display_list (tpl_2(my_list4));
      $display("Unzipped List 1:");
      display_list (my_list5);
      $display("Unzipped List 2:");
      display_list (my_list6);
      if ((my_list1 != my_list5) || (my_list2 != my_list6)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_UnZip
endpackage : UnZip
