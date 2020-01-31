
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


// module which implements a dual Gray code and and binary counter
// allowing increments or holds
module DualGrayCntr (
                 CLK,
                 RST,
                 INCR,
                 B_OUT,         // Binary code output
                 G_OUT          // Gray code output
                 );
   parameter             width = 1 ; // Minimum value = 1
   parameter             init = {width {1'b0}} ;

   input                 CLK ;
   input                 RST ;
   input                 INCR ;
   output [width -1 : 0] B_OUT ;
   output [width -1 : 0] G_OUT ;

   reg [width -1 : 0]    B_reg ;// flop variable
   reg [width -1 : 0]    G_reg ;// flop variable

   // combnational signals
   reg [width -1 : 0]    nextB;
   reg [width -1 : 0]    nextG;

   assign                G_OUT = G_reg ,
                         B_OUT = B_reg ;

   always @(posedge CLK or `BSV_RESET_EDGE RST)
     begin
        if (RST == `BSV_RESET_VALUE )
          begin
             B_reg <= `BSV_ASSIGNMENT_DELAY init ;
             G_reg <= `BSV_ASSIGNMENT_DELAY init ;
          end
        else if ( INCR )
          begin
             B_reg <= `BSV_ASSIGNMENT_DELAY nextB ;
             G_reg <= `BSV_ASSIGNMENT_DELAY nextG ;
          end
     end // always @ (posedge CLK)

   // Combinational block
   always @( B_reg )
     begin : incr_block
        nextB = B_reg + 1'b1 ;
        nextG = nextB ^ (nextB >> 1) ;
     end // block: incr_block

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        B_reg      = {((width + 1)/2){2'b10}} ;
        G_reg      = {((width + 1)/2){2'b10}} ;
      end
   // synopsys translate_on

   // Some assertions about parameter values
   initial
     begin : parameter_assertions
        integer ok ;
        ok = 1 ;

        if ( width <= `BSV_ASSIGNMENT_DELAY 0 )
          begin
             ok = 0;
             $display ( "ERROR DualGrayCntr.v: width parameter must be greater than 0" ) ;
          end

        if ( ok == 0 ) $finish ;

      end // initial begin
      // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // GrayCntr



`ifdef testBluespec
module testDualGrayCntr() ;
   parameter dsize = 5 ;

   wire      CLK ;
   wire [dsize -1 :0] BOUT ;
   wire [dsize -1 :0] GOUT ;

   reg                RST ;

   ClockGen#(20,10,10)  sysclk( CLK );

   initial
     begin
        RST = `BSV_RESET_VALUE ;
        $display( "running test" ) ;

        $dumpfile("DualGrayCntr.dump");
        $dumpvars(5) ;
        $dumpon ;
        #200 ;
        RST = !`BSV_RESET_VALUE ;

        #10000 $finish ;
     end

   DualGrayCntr #(dsize,0)
     dut( CLK, RST,  1'b1, BOUT, GOUT ) ;

   always @(negedge CLK)
     begin
        #1
         $display( "Cntr is: %b %b" , BOUT, GOUT ) ;
      end

endmodule
`endif
