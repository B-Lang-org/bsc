package Transpose;

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


function Int#(8) f (Int #(8) a,Int #(8) b,Int #(8) c);

    Int#(8) d = a + b +c ;
	return(d);
endfunction

module mkTestbench_Transpose();

   Vector #(5,Int #(8)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   Vector #(5,Int #(8)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   Vector #(5,Int #(8)) my_list3 = cons (10, cons (11, cons (12, cons (13, cons (14, nil)))));

   Vector #(3,Int #(8)) my_list1_t = cons (0, cons (5, cons (10, nil)));
   Vector #(3,Int #(8)) my_list2_t = cons (1, cons (6, cons (11, nil)));
   Vector #(3,Int #(8)) my_list3_t = cons (2, cons (7, cons (12, nil)));
   Vector #(3,Int #(8)) my_list4_t = cons (3, cons (8, cons (13, nil)));
   Vector #(3,Int #(8)) my_list5_t = cons (4, cons (9, cons (14, nil)));

   Vector #(3,Vector#(5,Int #(8))) my_list4 = cons (my_list1, cons (my_list2, cons (my_list3, nil)));
   Vector #(5,Vector#(3,Int #(8))) my_list5 = cons (my_list1_t, cons (my_list2_t, cons (my_list3_t, cons (my_list4_t, cons (my_list5_t,nil)))));

   Vector #(5,Vector#(3,Int #(8))) my_list6 = transpose(my_list4);


   rule fire_once (True);
      $display("List of List:");
      display_list (my_list4[0]);
      display_list (my_list4[1]);
      display_list (my_list4[2]);
      $display("Transposed List of Lists:");
      display_list (my_list6[0]);
      display_list (my_list6[1]);
      display_list (my_list6[2]);
      display_list (my_list6[3]);
      display_list (my_list6[4]);
      if (my_list5 != my_list6)
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Transpose
endpackage : Transpose
