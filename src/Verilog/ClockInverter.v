
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module ClockInverter(CLK_IN, PREEDGE,  CLK_OUT);

   input     CLK_IN;            // input clock
   output    PREEDGE;           // output signal announcing an upcoming edge
   output    CLK_OUT;           // output clock

   wire      CLK_OUT;
   wire      PREEDGE;
   
   assign    CLK_OUT = ! CLK_IN ;
   assign    PREEDGE = 1 ;
   
endmodule // ClockInverter

