package ZipWith3M;

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


function ActionValue#(Int#(8)) f (Int #(8) a,Int #(8) b,Int #(8) c);

	actionvalue
      noAction;
	  return(a+b+c);
	endactionvalue
endfunction

module mkTestbench_ZipWith3M();
   ListN #(5,Int #(8)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Int #(8)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   ListN #(5,Int #(8)) my_list3 = cons (10, cons (11, cons (12, cons (13, cons (14, nil)))));
   ListN #(5,Int #(8)) my_list4 = cons (15, cons (18, cons (21, cons (24, cons (27, nil)))));



   rule fire_once (True);
      ListN #(5,Int #(8)) my_list5 <- zipWith3M(f,my_list1,my_list2,my_list3); 
      $display("ListN1:");
      display_list (my_list1);
      $display("ListN2:");
      display_list (my_list2);
      $display("ListN3:");
      display_list (my_list3);
      $display("ZipWith3M ListN:");
      display_list (my_list5);
      if (my_list5 != my_list4) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipWith3M
endpackage : ZipWith3M
