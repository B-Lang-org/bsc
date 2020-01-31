
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module ProbeWire(OUT, IN);

   parameter size = 1;

   input  [size - 1 : 0] IN;
   output [size - 1 : 0] OUT;
   
   assign OUT = IN;

endmodule
