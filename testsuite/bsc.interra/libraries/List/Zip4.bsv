package Zip4;

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



module mkTestbench_Zip4();
   List #(UInt #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(UInt #(4)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Nil))));

   List #(Bool) my_list3 = Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Nil))))))))));
   List #(Bool) my_list4 = Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Nil)))))))));

   List #(Tuple4 #(UInt #(4), UInt #(4), Bool, Bool)) zipped_list = Cons (tuple4(1,2, True, False), Cons (tuple4(2,3, False, True), Cons (tuple4(3,4, True, False), Cons (tuple4(4,5, False, True), Nil))));


  
   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("List3:");
      display_list (my_list3);
      $display("List4:");
      display_list (my_list4);
      $display("Zipped List");
      display_list (zip4 (my_list1, my_list2, my_list3, my_list4));
      if (zipped_list != zip4(my_list1, my_list2, my_list3, my_list4)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Zip4




endpackage : Zip4
