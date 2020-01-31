
module CrossingBypassWire(CLK, WGET, WVAL);

   parameter width = 1;

   input     CLK;
   
   input [width - 1 : 0]    WVAL;

   output [width - 1 : 0]   WGET;

   assign WGET = WVAL;

endmodule
