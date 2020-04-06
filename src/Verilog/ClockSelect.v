
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


// A separate module which instantiates clock selection logic
// It is expected that custom logic will replace this module
// in general use.
// Module selects between 2 clock.
// For safety an output reset is asserted whenever a
// new clock is selected.
module ClockSelect(
                   CLK,
                   RST,
                   SELECT,
                   SELECT_ENABLE,
                   A_CLK,
                   A_CLKGATE ,
                   B_CLK,
                   B_CLKGATE ,
                   CLK_OUT,
                   CLK_GATE_OUT ,
                   OUT_RST
                   ) ;

   parameter        RSTDELAY = 2  ; // Width of reset shift reg

   input            CLK ;
   input            RST ;
   input            SELECT;
   input            SELECT_ENABLE;

   input            A_CLK;
   input            A_CLKGATE ;
   input            B_CLK;
   input            B_CLKGATE ;

   output           CLK_OUT;
   output           CLK_GATE_OUT ;
   output           OUT_RST ;

   wire             not_changed;

   reg              select_out ;
   reg              select_out2 ;
   reg [RSTDELAY:0] reset_hold ;
   wire [RSTDELAY+1:0] next_reset = {reset_hold, ~ `BSV_RESET_VALUE} ;

   wire               new_clock ;


   assign             CLK_OUT = new_clock ;

   assign {new_clock, CLK_GATE_OUT } = select_out == 1'b1 ?
                                       { A_CLK,  A_CLKGATE } :
                                       { B_CLK,  B_CLKGATE } ;

   // Consider the clock select change when it *really* does change or
   //  when the select reset is asserted.
   assign not_changed = ! ( (select_out != select_out2) ||
                            (RST == `BSV_RESET_VALUE )
                            );

   assign OUT_RST = reset_hold[RSTDELAY] ;

   always @(posedge CLK or `BSV_RESET_EDGE RST )
     begin
        if ( RST == `BSV_RESET_VALUE )
           begin
              select_out  <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
              select_out2 <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
           end
        else
          begin
             if ( SELECT_ENABLE )
                begin
                   select_out <= `BSV_ASSIGNMENT_DELAY SELECT ;
                end
             select_out2 <= `BSV_ASSIGNMENT_DELAY select_out ;
          end
     end // always @ (posedge CLK or `BSV_RESET_EDGE RST )


   // Shift the reset hood register to generate a reset for some clock times
   always @(posedge new_clock or negedge not_changed )
     begin
        if (!not_changed)
          begin
              reset_hold <= `BSV_ASSIGNMENT_DELAY {(RSTDELAY + 1) {`BSV_RESET_VALUE}} ;
          end
        else
          begin
             reset_hold <= `BSV_ASSIGNMENT_DELAY next_reset[RSTDELAY:0];
          end
     end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
         #0 ;
         select_out  = 1'b0 ;
         select_out2 = 1'b0 ;
        // initialize out of reset forcing the designer to call reset
         reset_hold = {(RSTDELAY + 1) {~ `BSV_RESET_VALUE}} ;
      end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule
