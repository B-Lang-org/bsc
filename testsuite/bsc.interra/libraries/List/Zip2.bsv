package Zip2;

import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%b", abc);
    endaction
endfunction



function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction


//Testing Zip for lists with unequal lengths. Length of new list = smaller of the //two lengths

module mkTestbench_Zip2();

   List #(UInt #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(UInt #(4)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Nil))));

   List #(Tuple2 #(UInt #(4), UInt #(4))) zipped_list = Cons (tuple2(1,2), Cons (tuple2(2,3), Cons (tuple2(3,4), Cons (tuple2(4,5), Nil))));
   

  
   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("Zipped List");
      display_list (zip (my_list1, my_list2));
      
      if (zipped_list != zip(my_list1, my_list2)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Zip2



endpackage : Zip2
