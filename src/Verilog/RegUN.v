
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


// Basic register without reset.
module RegUN(CLK, EN, D_IN, Q_OUT);
   parameter width = 1;

   input     CLK;
   input     EN;
   input [width - 1 : 0] D_IN;

   output [width - 1 : 0] Q_OUT;
   reg [width - 1 : 0]    Q_OUT;

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      Q_OUT = {((width + 1)/2){2'b10}} ;
   end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

   
   always@(posedge CLK)
     begin
        if (EN)
          Q_OUT <= `BSV_ASSIGNMENT_DELAY D_IN;
     end
endmodule

