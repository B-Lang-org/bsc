package Design;

import BGetPut :: *;

module mkDesign(BGetPut #(Bit #(8))) ;
   BGetPut #(Bit #(8)) dut();
   mkBGetPut the_dut (dut);
   return dut;
endmodule: mkDesign


endpackage : Design
