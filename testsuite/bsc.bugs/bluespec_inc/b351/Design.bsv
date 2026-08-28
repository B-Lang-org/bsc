package Design;

import BGetPut :: *;
import GetPut :: *;

// BGetPut is a tuple, which is not a valid module interface, so expose its two
// sides through a named interface instead.
interface DesignIFC;
   interface BGet#(Bit#(8)) fst;
   interface Put#(Bit#(8))  snd;
endinterface

module mkDesign(DesignIFC) ;
   BGetPut #(Bit #(8)) dut();
   mkBGetPut the_dut (dut);
   interface fst = tpl_1(dut);
   interface snd = tpl_2(dut);
endmodule: mkDesign


endpackage : Design
