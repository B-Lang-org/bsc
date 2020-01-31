
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


// module which implements a Gray code counter allowing increments or holds
module GrayCntr (
                 CLK,
                 RST,
                 INCR,
                 Q_OUT
                 );
   parameter             width = 2 ; // Minimum value = 2
   parameter             init = {width {1'b0}} ;

   input                 CLK ;
   input                 RST ;
   input                 INCR ;
   output [width -1 : 0] Q_OUT ;

   reg [width -1 : 0]    Q_reg ;// flop variable
   reg                   toggle;

   // combnational signals
   reg [width -1 : 0]    flips ;

   assign                Q_OUT = Q_reg ;

   always @(posedge CLK or `BSV_RESET_EDGE RST)
     begin
        if (RST == `BSV_RESET_VALUE)
          begin
             Q_reg <= `BSV_ASSIGNMENT_DELAY init ;
             toggle <= `BSV_ASSIGNMENT_DELAY 0 ;
          end
        else begin
           if ( INCR )
             begin
                Q_reg <= `BSV_ASSIGNMENT_DELAY Q_reg ^ flips ;
                toggle <= `BSV_ASSIGNMENT_DELAY ~ toggle ;
             end
        end // else: !if(RST == `BSV_RESET_VALUE)
     end // always @ (posedge CLK)

   // Combinational block
   always @(Q_reg or toggle)
     begin : incr_block
        integer               i;
        reg [width - 1: 0]    tempshift;

        flips[0] = ! toggle ;
        for ( i = 1 ; i < (width - 1) ; i = i+1 )
          begin
             tempshift = Q_reg << (1 + width - i ) ;
             flips[i] =  toggle & Q_reg[i-1] & ~(| tempshift ) ;
          end
        tempshift = Q_reg << 2 ;
        flips[width-1] = toggle & ~(| tempshift ) ;

     end // block: incr_block

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        Q_reg      = {((width + 1)/2){2'b10}} ;
        toggle     = 1'b1 ;
      end
   // synopsys translate_on

   // synopsys translate_off
   // Some assertions about parameter values
   initial
     begin : parameter_assertions
        integer ok ;
        ok = 1 ;

        if ( width <= `BSV_ASSIGNMENT_DELAY 1 )
          begin
             ok = 0;
             $display ( "ERROR GrayCntr.v: width parameter must be greater than 1" ) ;
          end

        if ( ok == 0 ) $finish ;

      end // initial begin
      // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // GrayCntr



`ifdef testBluespec
module testGrayCntr() ;
   parameter dsize = 5 ;

   wire      CLK ;
   wire [dsize -1 :0] QOUT ;

   reg                RST ;

   ClockGen#(20,10,10)  sysclk( CLK );

   initial
     begin
        RST = `BSV_RESET_VALUE ;
        $display( "running test" ) ;

        $dumpfile("GrayCntr.dump");
        $dumpvars(5) ;
        $dumpon ;
        #200 ;
        RST = !`BSV_RESET_VALUE ;

        #10000 $finish ;
     end

   GrayCntr #(dsize,0)
     dut( CLK, RST,  1'b1, QOUT ) ;

   always @(negedge CLK)
     begin
        #1
         $display( "Cntr is: %b" , QOUT ) ;
      end

endmodule
`endif
