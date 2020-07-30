package Test;

import ArithModules ::*;

module tb ();
    AddSub_IFC dut <- mkAddSub;
    rule test (True);
       $display ("5+6=%d", dut.start (5,6,True));
       $finish (2'b00);
    endrule
endmodule : tb


endpackage : Test
