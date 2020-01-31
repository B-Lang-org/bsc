
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



// Depth N "loopy" FIFO (N > 1)
module SizedFIFOL0(CLK, RST, ENQ, FULL_N, DEQ, EMPTY_N, CLR);
   parameter p1depth = 2;
   parameter p2cntr_width = 2; // log2(p1depth+1)

   localparam truedepth = (p1depth >= 2) ? p1depth : 2;

   input     CLK;
   input     RST;
   input     CLR;
   input     ENQ;
   input     DEQ;
   output    FULL_N;
   output    EMPTY_N;

   reg       not_full;
   reg       not_empty;
   reg [p2cntr_width-1 : 0] count;

   assign                 EMPTY_N = not_empty;
   assign                 FULL_N = not_full || DEQ;

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin
        count      = 0 ;
        not_empty  = 1'b0;
        not_full   = 1'b1;
     end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS


   always @(posedge CLK `BSV_ARESET_EDGE_META)
     begin
        if (RST == `BSV_RESET_VALUE)
        begin
           count <= `BSV_ASSIGNMENT_DELAY 0 ;
           not_empty <= `BSV_ASSIGNMENT_DELAY 1'b0;
           not_full <= `BSV_ASSIGNMENT_DELAY 1'b1;
        end // if (RST == `BSV_RESET_VALUE)
        else
          begin
             if (CLR)
               begin
                  count <= `BSV_ASSIGNMENT_DELAY 0 ;
                  not_empty <= `BSV_ASSIGNMENT_DELAY 1'b0;
                  not_full <= `BSV_ASSIGNMENT_DELAY 1'b1;
               end // if (CLR)
             else begin
                if (DEQ && ! ENQ && not_empty )
                  begin
                     not_full <= `BSV_ASSIGNMENT_DELAY 1'b1;
                     not_empty <= `BSV_ASSIGNMENT_DELAY  count != 'b01  ;
                     count <= `BSV_ASSIGNMENT_DELAY count - 1'b1 ;
                  end // if (DEQ && ! ENQ && not_empty )
                else if (ENQ && ! DEQ && not_full )
                  begin
                     not_empty <= `BSV_ASSIGNMENT_DELAY 1'b1;
                     not_full <= `BSV_ASSIGNMENT_DELAY count != (truedepth - 1) ;
                     count <= `BSV_ASSIGNMENT_DELAY count + 1'b1 ;
                  end // if (ENQ && ! DEQ && not_full )
             end // else: !if(CLR)
          end // else: !if(RST == `BSV_RESET_VALUE)
     end // always @ (posedge CLK or `BSV_RESET_EDGE RST)

   // synopsys translate_off
   always@(posedge CLK)
     begin: error_checks
        reg deqerror, enqerror ;

        deqerror =  0;
        enqerror = 0;
        if (RST == ! `BSV_RESET_VALUE)
           begin
              if ( ! EMPTY_N && DEQ )
                begin
                   deqerror = 1 ;
                   $display( "Warning: SizedFIFOL0: %m -- Dequeuing from empty fifo" ) ;
                end
              if ( ! FULL_N && ENQ )
                begin
                   enqerror =  1 ;
                   $display( "Warning: SizedFIFOL0: %m -- Enqueuing to a full fifo" ) ;
                end
           end // if (RST == ! `BSV_RESET_VALUE)
     end // block: error_checks
   // synopsys translate_on

endmodule // SizedFIFOL0
