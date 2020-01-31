
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


module ConvertToZ( IN, CTL, OUT);

   parameter width = 1;
   input [width - 1 : 0] 	IN;
   input 			CTL;
   output [width - 1 : 0]       OUT;
   
   tri [width - 1 : 0] 		BUS;
   
   
   assign BUS = CTL ? IN : 'bz;
   assign OUT = BUS;
   
endmodule






