
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

`ifdef BSV_ASYNC_RESET
 `define BSV_ARESET_EDGE_META or `BSV_RESET_EDGE RST
`else
 `define BSV_ARESET_EDGE_META
`endif

`ifdef BSV_RESET_FIFO_HEAD
 `define BSV_ARESET_EDGE_HEAD `BSV_ARESET_EDGE_META
`else
 `define BSV_ARESET_EDGE_HEAD
`endif

// Depth 1 FIFO
module FIFO1(CLK,
             RST,
             D_IN,
             ENQ,
             FULL_N,
             D_OUT,
             DEQ,
             EMPTY_N,
             CLR
             );

   parameter width = 1;
   parameter guarded = 1'b1;
   input                  CLK;
   input                  RST;
   input [width - 1 : 0]  D_IN;
   input                  ENQ;
   input                  DEQ;
   input                  CLR ;

   output                 FULL_N;
   output [width - 1 : 0] D_OUT;
   output                 EMPTY_N;

   reg [width - 1 : 0]    D_OUT;
   reg                    empty_reg ;


   assign                 EMPTY_N = empty_reg ;


`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        D_OUT   = {((width + 1)/2) {2'b10}} ;
        empty_reg = 1'b0 ;
     end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS


   assign FULL_N = !empty_reg;

   always@(posedge CLK `BSV_ARESET_EDGE_META)
     begin
        if (RST == `BSV_RESET_VALUE)
          begin
             empty_reg <= `BSV_ASSIGNMENT_DELAY 1'b0;
          end // if (RST == `BSV_RESET_VALUE)
        else
           begin
              if (CLR)
                begin
                   empty_reg <= `BSV_ASSIGNMENT_DELAY 1'b0;
                end // if (CLR)
              else if (ENQ)
                begin
                   empty_reg <= `BSV_ASSIGNMENT_DELAY 1'b1;
                end // if (ENQ)
              else if (DEQ)
                begin
                   empty_reg <= `BSV_ASSIGNMENT_DELAY 1'b0;
                end // if (DEQ)
           end // else: !if(RST == `BSV_RESET_VALUE)
     end // always@ (posedge CLK or `BSV_RESET_EDGE RST)

   always@(posedge CLK `BSV_ARESET_EDGE_HEAD)
     begin
`ifdef BSV_RESET_FIFO_HEAD
        if (RST == `BSV_RESET_VALUE)
          begin
             D_OUT <= `BSV_ASSIGNMENT_DELAY {width {1'b0}} ;
          end
        else
`endif
           begin
              if (ENQ)
                D_OUT     <= `BSV_ASSIGNMENT_DELAY D_IN;
           end // else: !if(RST == `BSV_RESET_VALUE)
     end // always@ (posedge CLK or `BSV_RESET_EDGE RST)

   // synopsys translate_off
   always@(posedge CLK)
     begin: error_checks
        reg deqerror, enqerror ;

        deqerror =  0;
        enqerror = 0;
        if (RST == ! `BSV_RESET_VALUE)
           begin
              if ( ! empty_reg && DEQ )
                begin
                   deqerror = 1 ;
                   $display( "Warning: FIFO1: %m -- Dequeuing from empty fifo" ) ;
                end
              if ( ! FULL_N && ENQ && (!DEQ || guarded) )
                begin
                   enqerror =  1 ;
                   $display( "Warning: FIFO1: %m -- Enqueuing to a full fifo" ) ;
                end
           end // if (RST == ! `BSV_RESET_VALUE)
     end
   // synopsys translate_on

endmodule

