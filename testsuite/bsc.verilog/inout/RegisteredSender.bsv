package RegisteredSender;

import "BVI" RegisteredSender =
module mkRegisteredSender(RegisteredSender_ifc);
   default_clock clk(CLK);
   no_reset;
   ifc_inout iioo(OUT);
   method set (SETVAL) enable (EN);
   schedule set C set;
endmodule

interface RegisteredSender_ifc;
   method Inout#(int) iioo;
   method Action set(int value);
endinterface

endpackage
