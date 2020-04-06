
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


// A clock divider circuit.
// Division is based on the parameters, where
// Division is upper - lower + 1
// Duty cycle is :
//       let half = 1 << (width-1)
//       (upper - half) / upper - lower + 1
// E.g., (2,1,3) is a divide by 3  duty cycle  2/3
//       (2,0,3) is a divide by 4  duty cycle  2/4
//       (1,0,1) is a divide by 2, duty cycle  1/2
//       (3,1,5) is a divide by 5  duty cycle  2/5
//       (3,2,6) is a divide by 5  duty cycle  3/5
// The offset allow edges for separate modules to be determined
// relative to each other. a clock divider with offset 1 occurs one
// (fast) clock later than a clock with offset 0.
module GatedClockDiv(CLK_IN,
		     CLK_GATE_IN,
		     RST,
		     PREEDGE,
		     CLK_OUT,
		     CLK_GATE_OUT);

   parameter width = 2 ;        // must be sufficient to hold upper
   parameter lower = 1 ;        //
   parameter upper = 3 ;
   parameter offset = 0;        // offset for relative edges.
                                // (0 <= offset <= (upper - lower)

   input     CLK_IN ;           // input clock
   input     CLK_GATE_IN ;
   input     RST ;

   output    PREEDGE ;          // output signal announcing an upcoming edge
   output    CLK_OUT ;          // output clock
   output    CLK_GATE_OUT ;

   reg [ width -1 : 0 ] cntr ;
   reg                  PREEDGE ;

   reg                  new_gate ;

   // Wire constants for the parameters
   wire [width-1:0]     upper_w ;
   wire [width-1:0]     lower_w ;

   assign               CLK_OUT = cntr[width-1] & new_gate;
   assign               CLK_GATE_OUT = new_gate ;
   assign               upper_w = upper ;
   assign               lower_w = lower ;

   // The clock is about to tick when counter is about to set its msb
   //  Note some simulators do not allow 0 width expressions
   wire [width-1:0]     nexttick = ~ ( 'b01 << (width-1) )  ;

   // Combinational block to generate next edge signal
   always@( cntr or nexttick )
     begin
        #1
        // The nonblocking assignment use to delay the update of the edge ready signal
        // Since this read by other always blocks trigger by the output CLK_OUT of this module
        PREEDGE <= `BSV_ASSIGNMENT_DELAY  (cntr == nexttick) ;
     end

   always@( posedge CLK_IN or `BSV_RESET_EDGE RST )
     begin
        // The use of blocking assignment within this block insures
        // that the clock generated from cntr[MSB] occurs before any
        // LHS of nonblocking assignments also from CLK_IN occur.
        // Basically, this insures that CLK_OUT and CLK_IN occur within
        // the same phase of the execution cycle,  before any state
        // updates occur. see
        // http://www.sunburst-design.com/papers/CummingsSNUG2002Boston_NBAwithDelays.pdf

        if (RST == `BSV_RESET_VALUE )
          cntr = upper - offset ;
        else if ( cntr < upper_w )
          cntr = cntr + 1 ;
        else
          cntr = lower_w ;

     end // always@ ( posedge CLK_IN or `BSV_RESET_EDGE RST )

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
       cntr = (upper - offset) ;
       PREEDGE = 0 ;
       new_gate = 0 ;
    end // initial begin
  // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS


endmodule // ClockDiv
