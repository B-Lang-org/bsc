
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



// A synchronization module for resets.   Output resets are held for
// RSTDELAY+1 cycles, RSTDELAY >= 0.   Both assertion and deassertions is
// synchronized to the clock.
module SyncReset (
                  IN_RST,
                  CLK,
                  OUT_RST
                  );

   parameter          RSTDELAY = 1  ; // Width of reset shift reg

   input              CLK ;
   input              IN_RST ;
   output             OUT_RST ;

   reg [RSTDELAY:0]   reset_hold ;
   wire [RSTDELAY+1:0] next_reset = {reset_hold, ~ `BSV_RESET_VALUE} ;

   assign  OUT_RST = reset_hold[RSTDELAY] ;

   always @( posedge CLK )      // reset is read synchronous with clock
     begin
       // The ternary assignment and the expansion of IN_RST ensure that the synchronizer is
       // X-pessimistic. It will immediately go to X when its input goes to X and will stay X
       // after the reset becomes defined until the Xs flush through the hold register.
       reset_hold <= `BSV_ASSIGNMENT_DELAY (IN_RST == `BSV_RESET_VALUE) ? {(RSTDELAY + 1) {IN_RST}}
                                                                        : next_reset[RSTDELAY:0];
     end // always @ ( posedge CLK )

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        #0 ;
        // initialize out of reset forcing the designer to do one
        reset_hold = {(RSTDELAY + 1) {~ `BSV_RESET_VALUE }} ;
     end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // SyncReset
