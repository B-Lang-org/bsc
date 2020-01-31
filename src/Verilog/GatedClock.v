
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


// Bluespec primitive module which gates a clock
// To avoid glitches, CLK_GATE_OUT only changes  when CLK_IN is low.
// CLK_GATE_OUT follows CLK_GATE_IN in the same cycle, but COND is first
// registered, thus delaying the gate condition by one cycle.
// In this model, the oscillator CLK_OUT stop when the CLK_GATE_IN or
// COND are deasserted.
module GatedClock(
		  // ports for the internal register
		  CLK,
		  RST,
                  COND,
		  COND_EN,
		  COND_OUT,

		  // ports for the input clock being gated
		  CLK_IN,
		  CLK_GATE_IN,

		  // ports for the output clock
                  CLK_OUT,
                  CLK_GATE_OUT );

   parameter init = 1 ;

   input  CLK ;
   input  RST ;
   input  COND ;
   input  COND_EN ;
   output COND_OUT ;

   input  CLK_IN ;
   input  CLK_GATE_IN ;

   output CLK_OUT ;
   output CLK_GATE_OUT ;

   reg    new_gate ;
   reg    COND_reg ;

   assign COND_OUT = COND_reg;

   assign CLK_OUT = CLK_IN & new_gate ;
   assign CLK_GATE_OUT = new_gate ;

   // Use latch to avoid glitches
   // Gate can only change when clock is low
   always @( CLK_IN or CLK_GATE_IN or COND_reg )
     begin
        if ( ! CLK_IN )
          new_gate <= `BSV_ASSIGNMENT_DELAY CLK_GATE_IN & COND_reg ;
     end

   // register the COND (asynchronous reset)
   always @( posedge CLK or `BSV_RESET_EDGE RST )
     begin
	if ( RST == `BSV_RESET_VALUE )
	  COND_reg <= `BSV_ASSIGNMENT_DELAY init ;
        else
          begin
             if ( COND_EN )
               COND_reg <= `BSV_ASSIGNMENT_DELAY COND ;
          end
     end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
      begin
	 #0 ;
         new_gate = 1'b0 ;
	 COND_reg = 1'b0 ;
      end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // GatedClock

