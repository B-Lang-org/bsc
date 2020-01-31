
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
// RSTDELAY+1 cycles, RSTDELAY >= 0.  Reset assertion is asynchronous,
// while deassertion is synchronized to the clock.
module SyncResetA (
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

   always @( posedge CLK or `BSV_RESET_EDGE IN_RST )
     begin
        if (IN_RST == `BSV_RESET_VALUE)
           begin
              reset_hold <= `BSV_ASSIGNMENT_DELAY {RSTDELAY+1 {`BSV_RESET_VALUE}} ;
           end
        else
          begin
             reset_hold <= `BSV_ASSIGNMENT_DELAY next_reset[RSTDELAY:0];
          end
     end // always @ ( posedge CLK or  `BSV_RESET_EDGE IN_RST )

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        #0 ;
        // initialize out of reset forcing the designer to do one
        reset_hold = {(RSTDELAY + 1) {~ `BSV_RESET_VALUE}} ;
     end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // SyncResetA
