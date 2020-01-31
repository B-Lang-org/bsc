
`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif



module SyncReset0 (
		   IN_RST,
		   OUT_RST
		   );

   input   IN_RST ;
   output  OUT_RST ;

   assign  OUT_RST = IN_RST ;

endmodule
