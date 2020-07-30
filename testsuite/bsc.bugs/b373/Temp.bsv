package Temp;

import Wallace :: *;
import List :: *;
import ListN :: *;
import ListReg :: *;

interface Design_IFC;
    method Bit #(1) sum ();   
endinterface

(* synthesize *)
module mkDesign (Design_IFC);
   
    
    List #(Bit #(1)) my_list1 = Cons (1, Cons (0, Nil));
    List #(Bit #(1)) my_list2 = Cons (1, Cons (1, Nil));
    Reg #(List #(Bit #(1))) reg_list1();
    mkListReg #(my_list1) the_reg_list1(reg_list1);    
    
    Reg #(List #(Bit #(1))) reg_list2();
    mkListReg #(my_list2) the_reg_list2(reg_list2);  
    
    List #(List #(Bit #(1))) list_of_bags = Cons (reg_list1, Cons(reg_list2, Nil));
    
    method sum ();
        sum = wallaceAddBags (toListN(list_of_bags));
    endmethod: sum

endmodule : mkDesign

endpackage : Temp
