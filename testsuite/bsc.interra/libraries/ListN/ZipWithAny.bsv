package ZipWithAny;

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


function Int#(6) f (Int #(6) a,Int #(6) b);

    Int#(6) c = a + b;
	return(c);
endfunction

module mkTestbench_ZipWithAny();
   ListN #(5,Int #(6)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(8,Int #(6)) my_list2 = 
                       cons (5, 
					   cons (6, 
					   cons (7, 
					   cons (8, 
					   cons (9, 
					   cons (10, 
					   cons (11, 
					   cons (12, nil))))))));

   ListN #(5,Int #(6)) my_list3 = cons (5, cons (7, cons (9, cons (11, cons (13, nil)))));
   ListN #(5,Int #(6)) my_list4 = zipWithAny(f,my_list1,my_list2);


   rule fire_once (True);
      $display("ListN1:");
      display_list (my_list1);
      $display("ListN2:");
      display_list (my_list2);
      $display("ZipWithAny ListN:");
      display_list (my_list4);
      if (my_list3 != my_list4) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipWithAny
endpackage : ZipWithAny
