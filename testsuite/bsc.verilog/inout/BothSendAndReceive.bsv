package BothSendAndReceive;
import SenderReceiver::*;

import "BVI" Both =
module mkBoth#(
   Integer outvalue, 
   Integer write_cyclenum, 
   Integer read_cyclenum,
   Integer loopat)(SingletonInout);
   
   default_clock(CLK);
   no_reset;
   ifc_inout iioo(INOUT);
   parameter readpt=read_cyclenum;
   parameter setpt=write_cyclenum;
   parameter loopat=loopat;
   parameter outvalue=outvalue;
endmodule
   
endpackage
