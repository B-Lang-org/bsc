import Cntrs::*;

(*synthesize, always_ready*)
module sysCntrSched ( Count#(Int#(5)));
   Count#(Int#(5)) cntr <- mkCount(0);
   return cntr;
endmodule
