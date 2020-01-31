
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


module SyncWire( DIN, DOUT );

   parameter width = 1;
            
   input [width - 1 : 0]    DIN;
   output [width - 1 : 0]   DOUT;

   assign                   DOUT = DIN ;
   

endmodule
