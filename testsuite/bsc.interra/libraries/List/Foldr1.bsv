//Shows how to use Foldr1 to calculate sum of first five elements of a list
package Foldr1;

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

function Int #(5) add (Int #(5) a, Int #(5) b);
    return (a + b);
endfunction

module mkTestbench_Foldr1();
   List #(Int #(5)) my_list1 = Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Nil)))));


  
   rule fire_once (True);
      $display("Sum of list of first five integers = %d", foldr1 (add, my_list1));
      if (foldr1(add,my_list1) != 15) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Foldr1
endpackage : Foldr1
