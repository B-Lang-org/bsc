package Sink;

import Pull :: *;

module mkDesign1 (Pull #(Bit #(8)));
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);
    
    method pull();
       actionvalue
         counter <= counter + 1;
         return counter * counter;
       endactionvalue
   endmethod: pull
endmodule : mkDesign1

module mkTestbench_Sink ();
    Pull #(Bit #(8)) src();
    mkDesign1 the_src(src);
    Empty des();
    sink #(src) the_des(des);
    return des;
endmodule : mkTestbench_Sink


endpackage : Sink
