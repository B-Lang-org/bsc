package WallaceAdd;

import Wallace :: *;
import List :: *;
import Vector :: *;
import ListReg :: *;

interface Design_IFC;
    method Bit #(10) sum ();   
endinterface

module mkDesign_WallaceAdd (Design_IFC);
   
    List #(Bit #(5)) my_list = Cons (5, Cons (30, Cons (4, Cons (6, Cons (9, Cons (11, Cons (12, Cons (13, Cons (0, Nil)))))))));
    
    Reg #(List #(Bit #(5))) reg_list();
    mkListReg #(my_list) the_reg_list(reg_list);    
    
    
    method sum ();
        sum = wallaceAdd (reg_list);
    endmethod: sum

endmodule : mkDesign_WallaceAdd

module mkTestbench_WallaceAdd ();

    Design_IFC dut();
    mkDesign_WallaceAdd the_dut (dut);

    rule fire_once (True);
        if (dut.sum == 10'd90)
            $display ("Simulation Passes");
        else
            $display ("Simulation Fails");
        $finish (2'b00);
    endrule
        
    

endmodule : mkTestbench_WallaceAdd

endpackage : WallaceAdd
