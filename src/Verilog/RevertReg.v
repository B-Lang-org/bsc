
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module RevertReg(CLK, Q_OUT, D_IN, EN);

   parameter width = 1;
   parameter init  = { width {1'b0} } ;

   input     CLK;
   input     EN;
   input [width - 1 : 0] D_IN;
   output [width - 1 : 0] Q_OUT;

   assign Q_OUT = init;
endmodule
