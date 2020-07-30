package Foldn;

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

function Bit #(8) my_add (Bit #(8) a, Bit #(8) b);
    return a + b;
endfunction

//The function below returns the maximum of first two elements of the list, together with the list minus the first two elements.

function Tuple2 #(Bit #(8), List #(Bit #(8))) f (List #(Bit #(8)) xs);
     return tuple2(max(head(xs), head(tail(xs))), tail (tail(xs)));
endfunction


module mkTestbench_Foldn();
   List #(Bit #(8)) my_list1 =  Cons (11, Cons (12, Cons (48, Cons (14, Cons (15, Cons (16, Cons (17, Cons (18, Nil))))))));
   Bit #(8)  result = foldn (f, my_list1); //Note that this can be applied only on lists with lengths equal to a power of two.

   rule fire_once (True);
      $display("Original List:");
      display_list(my_list1);
      $display("Maximum Element in the List:%d", result);
      if (result != 48)
         $display("Simulation Fails");
      else
         $display("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Foldn
endpackage : Foldn
