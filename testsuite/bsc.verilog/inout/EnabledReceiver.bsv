package EnabledReceiver;

import "BVI" EnabledReceiver =
module mkEnabledReceiver(EnabledReceiver_ifc);
   default_clock clk(CLK);
   no_reset;
   ifc_inout iioo(IN);
   method display_it () enable (EN);
   schedule display_it CF display_it;  
endmodule

interface EnabledReceiver_ifc;
   method Inout#(int) iioo;
   method Action display_it();
endinterface

endpackage
