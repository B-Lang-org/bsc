
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


module ConvertFromZ( IN, OUT);
   
   parameter width = 1;
   input [width - 1 : 0]       IN;
   output [width - 1 : 0]      OUT;
   
   tri [width - 1 : 0]  BUS;
   
   assign BUS = IN;
   assign OUT = BUS;
   
endmodule


