
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


module LatchCrossingReg(SCLK, SRST, EN, D_IN, Q_OUT, DCLK, L_OUT);

   parameter width = 1;
   parameter init  = { width {1'b0} } ;

   input                  SCLK;
   input                  SRST;
   input                  EN;
   input  [width - 1 : 0] D_IN;
   output [width - 1 : 0] Q_OUT;

   input                  DCLK;
   output [width - 1 : 0] L_OUT;

   reg [width - 1 : 0]    Q_OUT; // flop
   reg [width - 1 : 0]    L_OUT; // latch

   // flop in source clock domain
   always@(posedge SCLK)
     begin
	if (SRST == `BSV_RESET_VALUE)
          Q_OUT <= `BSV_ASSIGNMENT_DELAY init;
        else
          begin
             if (EN)
               Q_OUT <= `BSV_ASSIGNMENT_DELAY D_IN;
          end // else: !if(SRST == `BSV_RESET_VALUE)
     end

   // latch in destination clock domain
   always@(DCLK or Q_OUT)
     begin
        if (DCLK)
          L_OUT <= `BSV_ASSIGNMENT_DELAY Q_OUT;
     end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      Q_OUT = {((width + 1)/2){2'b10}} ;
   end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule
