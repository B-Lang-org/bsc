
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


module RWire(WGET, WHAS, WVAL, WSET);


   parameter width = 1;

   input [width - 1 : 0]    WVAL;
   input                    WSET;

   output [width - 1 : 0]   WGET;
   output                   WHAS;

   assign WGET = WVAL;
   assign WHAS = WSET;

endmodule
