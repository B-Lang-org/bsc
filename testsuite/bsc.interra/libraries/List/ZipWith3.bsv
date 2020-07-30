package ZipWith3;

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

function UInt #(4) f (UInt #(4) a, UInt #(4) b, Bool c);
    if (c) 
       return (a+b);
    else
       return 0;
endfunction

module mkTestbench_ZipWith3();
   List #(UInt #(4)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));
   List #(UInt #(4)) my_list2 = Cons (2, Cons (3, Cons (4, Cons (5, Nil))));

   List #(Bool) my_list3 = Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Cons (True, Cons (False, Nil))))))))));

   List #(UInt #(4)) zipped_list = Cons (3, Cons (0, Cons (7, Cons (0, Nil))));


  
   rule fire_once (True);
      $display("List1:");
      display_list (my_list1);
      $display("List2:");
      display_list (my_list2);
      $display("List3:");
      display_list (my_list3);
      $display("Zipped List (Add list1, list2 if corresponding element in list 3 is True)");
      display_list (zipWith3 (f,my_list1, my_list2, my_list3));
      if (zipped_list != zipWith3(f,my_list1, my_list2, my_list3)) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_ZipWith3




endpackage : ZipWith3
