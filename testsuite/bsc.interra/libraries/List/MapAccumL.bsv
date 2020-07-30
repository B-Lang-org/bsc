package MapAccumL;

import List :: *;

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


function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Action display_list1 (List #(Tuple2#(a,a)) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc1, my_list));
     endaction
endfunction


function Tuple2#(Int#(8),Int#(8)) f (Int #(8) a,Int #(8) b);

    Tuple2#(Int#(8),Int#(8)) c = tuple2(a+2*b,(a+b));
	return(c);
endfunction

module mkTestbench_MapAccumL();
   List #(Int #(8)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   List #(Int #(8)) my_list2 = cons (5, cons (6, cons (9, cons (14, cons (21, nil)))));

   Tuple2 #(Int#(8),List#(Int #(8))) result = mapAccumL(f,5,my_list1);



   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("MapAccumL List1:");
      display_list (tpl_2(result));
	  $display("Accumaltor = %d",tpl_1(result));
      if ((my_list2 != tpl_2(result)) || (tpl_1(result) != 25)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_MapAccumL
endpackage : MapAccumL
