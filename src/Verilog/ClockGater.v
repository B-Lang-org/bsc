
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
// In this model, the oscillator CLK_OUT does *not* stop when the CLK_GATE_IN or
// COND are deasserted.
module ClockGater(
		  // ports for the internal register
		  CLK,
		  RST,
                  COND,
		  // ports for the output clock
                  CLK_OUT,
                  CLK_GATE_OUT );

   parameter init = 1 ;

   input  CLK ;
   input  RST ;
   input  COND ;
   output CLK_OUT ;
   output CLK_GATE_OUT ;

   // BUFG buf_gC(.I(CLK), .O(CLK_OUT));
   assign CLK_OUT = CLK;
   //BUFG buf_gG(.I(COND),   .O(CLK_GATE_OUT));
   assign CLK_GATE_OUT = COND;
endmodule // GatedClock
