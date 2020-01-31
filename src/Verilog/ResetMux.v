
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

// A separate module which instantiates a simple reset muxing primitive.
// The primitive includes an internal register which maintains the selector
// state.
module ResetMux(
                CLK,
                SELECT,
                SELECT_ENABLE,
                A_RST,
                B_RST,
                RST_OUT
               ) ;

   input            CLK;
   input            SELECT;
   input            SELECT_ENABLE;

   input            A_RST;
   input            B_RST;

   output           RST_OUT;

   reg sel_reg;

   assign RST_OUT = (sel_reg == 1'b1) ? A_RST : B_RST ;

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
