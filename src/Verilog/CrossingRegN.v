
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


module CrossingRegN(CLK, RST, Q_OUT, D_IN, EN);

   parameter width = 1;
   parameter init  = { width {1'b0} } ;

   input     CLK;
   input     RST;
   input     EN;
   input [width - 1 : 0] D_IN;
   output [width - 1 : 0] Q_OUT;

   reg [width - 1 : 0]    Q_OUT;

   always@(posedge CLK)
     begin
        if (RST == `BSV_RESET_VALUE)
          Q_OUT <= `BSV_ASSIGNMENT_DELAY init;
        else
          begin
             if (EN)
               Q_OUT <= `BSV_ASSIGNMENT_DELAY D_IN;
          end // else: !if(RST == `BSV_RESET_VALUE)
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

