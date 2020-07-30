package Sink;

import RPush :: *;

module mkTestbench_Sink (RPush #(Bit #(8)));
    RPush #(Bit #(8)) dut();
    sink the_dut(dut);
    return dut;
endmodule : mkTestbench_Sink

endpackage : Sink
