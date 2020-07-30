package Scanl;

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

function Bit #(16) my_mult (Bit #(16) b, Bit #(8) a);
   return (zeroExtend (a) * b);
endfunction


module mkTestbench_Scanl();
   List #(Bit #(8)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Cons (7, Nil)))))));
   List #(Bit #(16)) my_list2 = Cons (1, Cons (1, Cons (2, Cons (6, Cons (24, Cons (120, Cons (720, Cons (5040, Nil))))))));

   List #(Bit #(16)) my_list3 = scanl (my_mult, 16'd1, my_list1);

   rule fire_once (True);
      $display("Original List:");
      display_list(my_list1);
      $display("Scanned List (Factorial):");
      display_list(my_list3);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Scanl
endpackage : Scanl
