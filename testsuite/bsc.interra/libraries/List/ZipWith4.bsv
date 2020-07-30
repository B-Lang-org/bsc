package ZipWith4;

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

function UInt #(4) f (UInt #(4) a, UInt #(4) b, Bool c, Bool d);
     if (c && !d)
        return (a+b);
     else
        return (0);
endfunction

module mkTestbench_ZipWith4();
   List #(UInt #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(UInt #(4)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Nil))));

   List #(Bool) my_list3 = Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Nil))))))))));
   List #(Bool) my_list4 = Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Nil)))))))));

   List #(UInt #(4)) zipped_list = Cons (3, Cons (0, Cons (7, Cons (0, Nil))));


  
   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("List3:");
      display_list (my_list3);
      $display("List4:");
      display_list (my_list4);
      $display("Zipped List:");
      display_list (zipWith4 (f,my_list1, my_list2, my_list3, my_list4));
      if (zipped_list != zipWith4(f,my_list1, my_list2, my_list3, my_list4)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipWith4




endpackage : ZipWith4
