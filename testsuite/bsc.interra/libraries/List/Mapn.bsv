package Mapn;

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

function Bit #(16) my_mult (Bit #(16) a, Bit #(8) b);
  return a * zeroExtend (b);
endfunction

function Tuple2 #(Bit #(16), List #(Bit #(8))) f (List #(Bit #(8)) xs);
    if (xs==Nil)
       return tuple2(0, Nil);
    else
       return tuple2(foldl (my_mult, 1, xs) , init (xs));
endfunction

module mkTestbench_Mapn();
   List #(Bit #(8)) my_list1 =  Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Cons (7, Cons (8, Cons (9, Nil)))))))));
   List #(Bit #(16)) my_list2 = Cons (1, Cons (2, Cons (6, Cons (24, Cons (120, Cons (720, Cons (5040, Cons (40320, Cons (35200,  Nil)))))))));
   List #(Bit #(16)) my_list3 = reverse (mapn (f, my_list1));

   rule fire_once (True);
      $display("Original List:");
      display_list(my_list1);
      $display("Factorial List:");
      display_list(my_list3);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Mapn
endpackage : Mapn
