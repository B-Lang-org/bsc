// This module is not synthesizable.

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



// A generator for resets from an absolute clock, starting at
// time 0. The output reset is held for RSTHOLD cycles, RSTHOLD > 0.

module InitialReset (
                     CLK,
                     OUT_RST
                     );

   parameter          RSTHOLD = 2  ; // Width of reset shift reg

   input              CLK ;
   output             OUT_RST ;

   // synopsys translate_off

   reg [RSTHOLD-1:0]  reset_hold ;
   wire [RSTHOLD:0] next_reset = {reset_hold, ~ `BSV_RESET_VALUE} ;

   assign  OUT_RST = reset_hold[RSTHOLD-1] ;

   always @( posedge CLK )
     begin
        reset_hold <= `BSV_ASSIGNMENT_DELAY next_reset[RSTHOLD-1:0];
     end // always @ ( posedge CLK )

   initial
     begin
       #0 // Required so that negedge is seen by any derived async resets
       reset_hold = { RSTHOLD { `BSV_RESET_VALUE }} ;  // all bits to reset value
     end


   // synopsys translate_on

endmodule // InitialReset

