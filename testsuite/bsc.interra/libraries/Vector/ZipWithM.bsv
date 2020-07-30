package ZipWithM;

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


function ActionValue#(Int#(6)) f (Int #(6) a,Int #(6) b);

//    Int#(6) c ;
	actionvalue
   //   c = a + b;
      noAction;
	  return(a+b);
	endactionvalue
endfunction

module mkTestbench_ZipWithM();
   Vector #(5,Int #(6)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   Vector #(5,Int #(6)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   Vector #(5,Int #(6)) my_list3 = cons (5, cons (7, cons (9, cons (11, cons (13, nil)))));



   rule fire_once (True);
      Vector #(5,Int #(6)) my_list4 <- zipWithM(f,my_list1,my_list2); 
      $display("ListN1:");
      display_list (my_list1);
      $display("ListN2:");
      display_list (my_list2);
      $display("ZipWith Vector:");
      display_list (my_list4);
      if (my_list3 != my_list4) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipWithM
endpackage : ZipWithM
