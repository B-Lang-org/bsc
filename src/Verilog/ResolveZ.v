
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module ResolveZ( IN_0, IN_1, OUT);
   
   parameter width = 1;

   input [width - 1 : 0] IN_0;
   input [width - 1 : 0] IN_1;

   output [width - 1 : 0] OUT;

   tri [width - 1 : 0] 	BUS;
   
   assign BUS = IN_0 ;
   assign BUS = IN_1 ;
   assign OUT = BUS  ;   
   
endmodule


