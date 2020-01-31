
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


// A clock synchronization FIFO where the enqueue and dequeue sides are in
// different clock domains.
// The depth of the FIFO is strictly 1 element.   Implementation uses only
// 1 register to minimize hardware
// There are no restrictions w.r.t. clock frequencies
// FULL and EMPTY signal are pessimistic, that is, they are asserted
// immediately when the FIFO becomes FULL or EMPTY, but their deassertion
// is delayed due to synchronization latency.
module SyncFIFO1(
                 sCLK,
                 sRST,
                 dCLK,
                 sENQ,
                 sD_IN,
                 sFULL_N,
                 dDEQ,
                 dD_OUT,
                 dEMPTY_N
                 ) ;

   parameter                 dataWidth = 1 ;

   // input clock domain ports
   input                     sCLK ;
   input                     sRST ;
   input                     sENQ ;
   input [dataWidth -1 : 0]  sD_IN ;
   output                    sFULL_N ;

   // destination clock domain ports
   input                     dCLK ;
   input                     dDEQ ;
   output                    dEMPTY_N ;
   output [dataWidth -1 : 0] dD_OUT ;

   // FIFO DATA
   reg [dataWidth -1 : 0]    syncFIFO1Data ;

   // Reset generation
   wire                      dRST = sRST;

   // sCLK registers
   reg                       sEnqToggle,  sDeqToggle, sSyncReg1;
   // dCLK registers
   reg                       dEnqToggle,  dDeqToggle, dSyncReg1;

   // output assignment
   assign dD_OUT = syncFIFO1Data;
   assign dEMPTY_N = dEnqToggle != dDeqToggle;
   assign sFULL_N  = sEnqToggle == sDeqToggle;

   always @(posedge sCLK or `BSV_RESET_EDGE sRST) begin
      if (sRST == `BSV_RESET_VALUE) begin
         syncFIFO1Data <= `BSV_ASSIGNMENT_DELAY  {dataWidth {1'b0}};
         sEnqToggle    <= `BSV_ASSIGNMENT_DELAY  1'b0;
         sSyncReg1     <= `BSV_ASSIGNMENT_DELAY  1'b0;
         sDeqToggle    <= `BSV_ASSIGNMENT_DELAY  1'b1; // FIFO marked as full during reset
      end
      else begin
         if (sENQ && (sEnqToggle == sDeqToggle)) begin
            syncFIFO1Data <= `BSV_ASSIGNMENT_DELAY sD_IN;
            sEnqToggle    <= `BSV_ASSIGNMENT_DELAY ! sEnqToggle;
         end
         sSyncReg1  <= `BSV_ASSIGNMENT_DELAY dDeqToggle; // clock domain crossing
         sDeqToggle <= `BSV_ASSIGNMENT_DELAY sSyncReg1;
      end
   end

   always @(posedge dCLK or `BSV_RESET_EDGE dRST) begin
      if (dRST == `BSV_RESET_VALUE) begin
         dEnqToggle    <= `BSV_ASSIGNMENT_DELAY  1'b0;
         dSyncReg1     <= `BSV_ASSIGNMENT_DELAY  1'b0;
         dDeqToggle    <= `BSV_ASSIGNMENT_DELAY  1'b0;
      end
      else begin
         if (dDEQ && (dEnqToggle != dDeqToggle)) begin
            dDeqToggle    <= `BSV_ASSIGNMENT_DELAY ! dDeqToggle;
         end
         dSyncReg1  <= `BSV_ASSIGNMENT_DELAY sEnqToggle; // clock domain crossing
         dEnqToggle <= `BSV_ASSIGNMENT_DELAY dSyncReg1;
      end
   end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin : initBlock
      syncFIFO1Data = {((dataWidth + 1)/2){2'b10}} ;
      sEnqToggle = 1'b0;
      sDeqToggle = 1'b0;
      sSyncReg1 = 1'b0;

      dEnqToggle = 1'b0;
      dDeqToggle = 1'b0;
      dSyncReg1 = 1'b0;
   end
   // synopsys translate_on
`endif // !`ifdef BSV_NO_INITIAL_BLOCKS

   // synopsys translate_off
   always@(posedge sCLK)
     begin: error_checks1
        reg enqerror ;
        enqerror = 0;
        if (sRST == ! `BSV_RESET_VALUE)
          begin
             if ( sENQ && (sEnqToggle != sDeqToggle)) begin
                enqerror = 1;
                $display( "Warning: SyncFIFO1: %m -- Enqueuing to a full fifo" ) ;
             end
          end
     end

   always@(posedge dCLK)
     begin: error_checks2
        reg deqerror ;
        deqerror = 0;
        if (dRST == ! `BSV_RESET_VALUE)
          begin
             if ( dDEQ && (dEnqToggle == dDeqToggle)) begin
                deqerror = 1;
                $display( "Warning: SyncFIFO1: %m -- Dequeuing from an empty full fifo" ) ;
             end
          end
     end // block: error_checks
   // synopsys translate_on

endmodule
