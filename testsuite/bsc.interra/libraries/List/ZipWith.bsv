//Uses zipWith to add corresponding elements of two lists
package ZipWith;

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

function Bit #(4) my_add(Bit #(4) a, Bit #(4) b);
     return a + b;
endfunction

module mkTestbench_ZipWith();

   List #(Bit #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(Bit #(4)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Nil))));

   List #(Bit #(4)) zipped_list = Cons (3, Cons (5, Cons (7, Cons (9, Nil))));
   


  
   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("Zipped List");
      display_list (zipWith (my_add, my_list1, my_list2));
      
      if (zipped_list != zipWith (my_add, my_list1, my_list2)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipWith



endpackage : ZipWith
