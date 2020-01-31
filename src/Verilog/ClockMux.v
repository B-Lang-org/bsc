
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

// A separate module which instantiates a simple clock muxing primitive.
// The primitive includes an internal register which maintains the selector
// state.
module ClockMux(
                CLK,
                SELECT,
                SELECT_ENABLE,
                A_CLK,
                A_CLKGATE ,
                B_CLK,
                B_CLKGATE ,
                CLK_OUT,
                CLK_GATE_OUT
               ) ;

   input            CLK;
   input            SELECT;
   input            SELECT_ENABLE;

   input            A_CLK;
   input            A_CLKGATE ;
   input            B_CLK;
   input            B_CLKGATE ;

   output           CLK_OUT;
   output           CLK_GATE_OUT ;

   reg sel_reg;

   assign {CLK_OUT, CLK_GATE_OUT } = sel_reg == 1'b1 ?
                                     { A_CLK,  A_CLKGATE } :
                                     { B_CLK,  B_CLKGATE } ;
   

   always @(posedge CLK)
   begin
     if (SELECT_ENABLE)
       sel_reg <= SELECT;
   end

      
`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
      begin
         #0 ;
         sel_reg  = 1'b0 ;
      end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule                
