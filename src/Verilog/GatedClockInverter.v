
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module GatedClockInverter(CLK_IN, CLK_GATE_IN, PREEDGE, CLK_OUT, CLK_GATE_OUT);

   input     CLK_IN;            // input clock
   input     CLK_GATE_IN;
   output    PREEDGE;           // output signal announcing an upcoming edge
   output    CLK_OUT;           // output clock
   output    CLK_GATE_OUT;

   reg       new_gate;

   wire      CLK_OUT;
   wire      CLK_GATE_OUT;
   wire      PREEDGE;
   
   assign    CLK_OUT = (! CLK_IN) & new_gate;
   assign    CLK_GATE_OUT = new_gate;
   assign    PREEDGE = 1 ;

   // Use latch to avoid glitches
   // Gate can only change when clock is low
   always @( CLK_OUT or CLK_GATE_IN )
     begin
        if ( ! CLK_OUT )
          new_gate <= `BSV_ASSIGNMENT_DELAY CLK_GATE_IN ;
     end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
  // synopsys translate_off
  initial
    begin
       #0 ;
       new_gate = 1 ;
    end // initial begin   
  // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS
   
endmodule // GatedClockInverter
