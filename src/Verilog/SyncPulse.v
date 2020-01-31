
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


// A pulse based clock domain synchronization scheme.
// When a sEN is asserted, a pulse is eventually sent to dPulse in the
// destination clock domain.
// Close and Multiple asserts of sEN may not be seen at the destination side.
// Reset signal is not needed since it a pulse-based, rather than
// level-based protocol
// Delay is 2 dCLK cycle.
// dPulse is not registered.
module SyncPulse(
                  sCLK,
                  sRST,
                  dCLK,
                  sEN,
                  dPulse
                  );

   // source clock ports
   input     sCLK ;
   input     sRST ;
   input     sEN ;

   // destination clock ports
   input     dCLK ;
   output    dPulse ;

   // Flops to hold data
   reg       sSyncReg;
   reg       dSyncReg1, dSyncReg2;
   reg       dSyncPulse;

   assign    dPulse = dSyncReg2 != dSyncPulse ;

   always @(posedge sCLK or `BSV_RESET_EDGE sRST)
     begin
        if (sRST == `BSV_RESET_VALUE)
          sSyncReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
        else
          begin
             if ( sEN )
               begin
                  sSyncReg <= `BSV_ASSIGNMENT_DELAY ! sSyncReg ;
               end
          end // else: !if(sRST == `BSV_RESET_VALUE)
     end // always @ (posedge sCLK or `BSV_RESET_EDGE sRST)


   always @(posedge dCLK or `BSV_RESET_EDGE sRST )
      begin
         if (sRST == `BSV_RESET_VALUE)
            begin
               dSyncReg1 <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
               dSyncReg2 <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
               dSyncPulse <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
            end // if (sRST == `BSV_RESET_VALUE)
         else
           begin
              dSyncReg1 <= `BSV_ASSIGNMENT_DELAY sSyncReg ;// domain crossing
              dSyncReg2 <= `BSV_ASSIGNMENT_DELAY dSyncReg1 ;
              dSyncPulse <= `BSV_ASSIGNMENT_DELAY dSyncReg2 ;
           end // else: !if(sRST == `BSV_RESET_VALUE)
      end // always @ (posedge dCLK or `BSV_RESET_EDGE sRST )

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
      begin
         sSyncReg   = 1'b0 ;
         dSyncReg1  = 1'b0 ;
         dSyncReg2  = 1'b0 ;
         dSyncPulse = 1'b0 ;
      end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // PulseSync

