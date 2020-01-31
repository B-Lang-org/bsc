
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif



module RegTwoUN(CLK, ENA, D_INA, ENB, D_INB, Q_OUT);
   parameter width = 1;

   input     CLK ;
   input     ENA ;
   input     ENB ;
   input [width - 1 : 0] D_INA;
   input [width - 1 : 0] D_INB;

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

   
   always@(posedge CLK) begin
      if (ENA)
        Q_OUT <= `BSV_ASSIGNMENT_DELAY D_INA;
      else if (ENB)
        Q_OUT <= `BSV_ASSIGNMENT_DELAY D_INB;
   end 
   
endmodule

