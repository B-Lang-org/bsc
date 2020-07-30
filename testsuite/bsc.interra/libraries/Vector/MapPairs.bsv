package MapPairs;

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


function Int#(4) f (Int #(4) a,Int #(4) b);
    Int#(4) c = a + b;
	return(c);
endfunction

function Int#(4) g (Int #(4) a);
	return(a);
endfunction

module mkTestbench_MapPairs();
   Vector #(5,Int #(4)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   Vector #(3,Int #(4)) my_list2 = cons (1, cons (5, cons (4,nil)));
   Vector #(3,Int #(4)) my_list3 = mapPairs(f,g,my_list1);


   rule fire_once (True);
      $display("ListN1:");
      display_list (my_list1);
      $display("mapPaired Vector:");
      display_list (my_list3);
      if (my_list3 != my_list2) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_MapPairs
endpackage : MapPairs
