package Sortle;

import BitonicSort :: *;
import Vector :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%b", abc);
    endaction
endfunction



function Action display_list (Vector #(8 ,a) my_list) provisos (Bits # (a,sa));
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

function Bool le_bool (Bool x1, Bool x2) ; 
    if (x1 == False || (x1==True && x2==True))
       return True;
    else
       return False;
endfunction : le_bool

module mkTestbench_Sortle ();
    Vector #(8, UInt#(4)) list1 = cons (2, cons(8, cons(6, cons (15, cons (13, cons (2, cons (8, cons (9, nil))))))));
    Vector#(8, UInt#(4)) sorted_list1 = sortLe (le, list1);
    Vector #(8, UInt#(4)) expected_sorted_list1 = cons (2, cons(2, cons(6, cons (8, cons (8, cons (9, cons (13, cons (15, nil))))))));
    

    Vector #(8, Int#(4)) list2 = cons (-2, cons(0, cons(6, cons (5, cons (-3, cons (2, cons (6, cons (-1, nil))))))));
    Vector#(8, Int#(4)) sorted_list2 = sortLe (le, list2);
    Vector #(8, Int#(4)) expected_sorted_list2 = cons (-3, cons(-2, cons(-1, cons (0, cons (2, cons (5, cons (6, cons (6, nil))))))));
    
    Vector #(8, Bool) list3 = cons (False, cons(False, cons(True, cons (False, cons (True, cons (True, cons (True, cons (False, nil))))))));
    Vector#(8, Bool) sorted_list3 = sortLe (le_bool, list3);
    Vector #(8, Bool) expected_sorted_list3 = cons (False, cons(False, cons(False, cons (False, cons (True, cons (True, cons (True, cons (True, nil))))))));
    

    rule fire_once (True);
       $display ("Sorted List of Unsigned Integers=");
       display_list (sorted_list1);
       $display ("Sorted List of Signed Integers=");
       display_list (sorted_list2);
       $display ("Sorted List of Booleans");
       display_list (sorted_list3);
      
       if (sorted_list1 != expected_sorted_list1 || sorted_list2 != expected_sorted_list2 || sorted_list3 != expected_sorted_list3)
          $display ("Simulation Fails");
       else
          $display ("Simulation Passes");

       $finish(2'b00);
    endrule
endmodule : mkTestbench_Sortle

endpackage : Sortle
