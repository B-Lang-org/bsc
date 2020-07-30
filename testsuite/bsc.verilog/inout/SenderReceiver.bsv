package SenderReceiver;

import "BVI" Sender = 
module mkSender#(Integer outvalue)(SingletonInout);
   // even though the value is static,
   // we want to allow BSC to sample it on whatever clock it chooses
   default_clock clk();
   parameter outvalue=outvalue;
   ifc_inout iioo(OUT);
   no_reset;
endmodule

interface SingletonInout;
   method Inout#(int) iioo;
endinterface

import "BVI" Receiver =
module mkReceiver(SingletonInout);
   default_clock clk(CLK);
   no_reset;
   ifc_inout iioo(IN);
endmodule

endpackage
