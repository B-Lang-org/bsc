
import Cntrs::*;

(*synthesize*)
module sysCntrsLimits();

   UCount          bdut <- mkUCount(0,-1);

endmodule

(*synthesize*)
module sysCntrsLimits2();

   UCount          bdut2 <- mkUCount(0,5000000000);

endmodule
