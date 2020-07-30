package WallaceAddBags;

import Wallace :: *;
import List :: *;
import Vector :: *;
import ListReg :: *;

interface Design_IFC;
    method Bit #(5) sum ();   
endinterface

module mkDesign_WallaceAddBags (Design_IFC);
   
    List #(Bit #(1)) my_list1 = Cons (1, Cons (0, Nil));
    List #(Bit #(1)) my_list2 = Cons (1, Cons (1, Nil));
    List #(Bit #(1)) my_list3 = Cons (0, Cons (1, Nil));
    List #(Bit #(1)) my_list4 = Cons (1, Nil);
    List #(Bit #(1)) my_list5 = Nil;
    
    Reg #(List #(Bit #(1))) reg_list1();
    mkListReg #(my_list1) the_reg_list1(reg_list1);    
    
    Reg #(List #(Bit #(1))) reg_list2();
    mkListReg #(my_list2) the_reg_list2(reg_list2);  
    
    Reg #(List #(Bit #(1))) reg_list3();
    mkListReg #(my_list3) the_reg_list3(reg_list3); 

    Reg #(List #(Bit #(1))) reg_list4();
    mkListReg #(my_list4) the_reg_list4(reg_list4);    
    
    Reg #(List #(Bit #(1))) reg_list5();
    mkListReg #(my_list5) the_reg_list5(reg_list5);    
    

    Vector #(5, List #(Bit #(1))) list_of_bags = cons (reg_list1, cons(reg_list2, cons(reg_list3, cons (reg_list4, cons (reg_list5, nil)))));
    
    method sum ();
        sum = wallaceAddBags (list_of_bags);
    endmethod: sum

endmodule : mkDesign_WallaceAddBags

module mkTestbench_WallaceAddBags ();

    Design_IFC dut();
    mkDesign_WallaceAddBags the_dut (dut);

    rule fire_once (True);
        if (dut.sum == 5'd17)
            $display ("Simulation Passes");
        else
            $display ("Simulation Fails");
        $finish (2'b00);
    endrule
        
    

endmodule : mkTestbench_WallaceAddBags

endpackage : WallaceAddBags
