package Spew;

import Pull :: *;

module mkTestbench_Spew (Pull #(Bit #(8)));
    Pull #(Bit #(8)) dut();
    spew the_dut(dut);
    return dut;
endmodule : mkTestbench_Spew

endpackage : Spew
