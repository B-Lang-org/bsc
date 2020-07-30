//Appends to Lists of type UInt #(4).

package Append;

import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction



module mkTestbench_Append();
   List #(UInt #(4)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
   List #(UInt #(4)) my_list2 = Cons (5, Cons (6, Cons (7, Cons (8, Cons (9, Nil)))));
   List #(UInt #(4)) my_list3 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Cons (7, Cons (8, Cons (9, Nil))))))))));


   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("Appended List:");
      display_list (append(my_list1, my_list2));
      if (my_list3 != append (my_list1, my_list2)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Append
endpackage : Append
