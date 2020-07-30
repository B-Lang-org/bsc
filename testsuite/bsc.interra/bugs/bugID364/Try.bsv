package Try;

import BitonicSort :: *;
import Vector :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%b", abc);
    endaction
endfunction



function Action display_list (Vector #(7 ,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Bool le (a x1, a x2) provisos (Ord #(a)); 
    if (x1 <= x2)
       return True;
    else
       return False;
endfunction : le


module mkTestbench ();
    Vector #(7, UInt#(4)) list1 = cons(8, cons(6, cons (15, cons (13, cons (2, cons (8, cons (9, nil)))))));
    Vector#(7, UInt#(4)) sorted_list1 = sortLe (le, list1);
    Vector #(7, UInt#(4)) expected_sorted_list1 = cons(2, cons(6, cons (8, cons (8, cons (9, cons (13, cons (15, nil)))))));
    
    Reg #(Bool) simtest <- mkReg (False);

    rule fire_once (!simtest);
       simtest <= True;
       $display ("Sorted List of Unsigned Integers=");
       display_list (sorted_list1);
      
       if (sorted_list1 != expected_sorted_list1)
          $display ("Simulation Fails");
       else
          $display ("Simulation Passes");
    endrule
endmodule : mkTestbench

endpackage : Try
