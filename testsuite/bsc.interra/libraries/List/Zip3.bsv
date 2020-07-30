package Zip3;

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



module mkTestbench_Zip3();
   List #(UInt #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(UInt #(4)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Nil))));

   List #(Bool) my_list3 = Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Nil))))))))));

   List #(Tuple3 #(UInt #(4), UInt #(4), Bool)) zipped_list = Cons (tuple3(1,2, True), Cons (tuple3(2,3, False), Cons (tuple3(3,4, True), Cons (tuple3(4,5, False), Nil))));


  
   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("List3:");
      display_list (my_list3);
      $display("Zipped List");
      display_list (zip3 (my_list1, my_list2, my_list3));
      if (zipped_list != zip3(my_list1, my_list2, my_list3)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Zip3




endpackage : Zip3
