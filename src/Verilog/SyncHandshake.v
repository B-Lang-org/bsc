
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


//
// Transfer takes 2 dCLK to see data,
// sRDY recovers takes 2 dCLK + 2 sCLK
module SyncHandshake(
                     sCLK,
                     sRST,
                     dCLK,
                     sEN,
                     sRDY,
                     dPulse
                     );
   parameter init = 1'b0;
   parameter delayreturn = 1'b0;

   // Source clock port signal
   input     sCLK ;
   input     sRST ;
   input     sEN ;
   output    sRDY ;

   // Destination clock port signal
   input     dCLK ;
   output    dPulse ;

   // Flops to hold data
   reg       dSyncReg1, dSyncReg2 ;
   reg       dLastState ;
   reg       sToggleReg ;
   reg       sSyncReg1, sSyncReg2 ;

   // Output signal
   assign    dPulse = dSyncReg2 != dLastState ;
   assign    sRDY = sSyncReg2 == sToggleReg;
   wire      ackValue = delayreturn ? dLastState : dSyncReg2 ;

   always @(posedge sCLK or `BSV_RESET_EDGE sRST)
     begin
        if (sRST == `BSV_RESET_VALUE)
           begin
              sSyncReg1  <= `BSV_ASSIGNMENT_DELAY ! init ; // Reset hi so sRDY is low during reset
              sSyncReg2  <= `BSV_ASSIGNMENT_DELAY ! init ;
              sToggleReg <= `BSV_ASSIGNMENT_DELAY init ;
           end
        else
           begin

              // hadshake return synchronizer
              sSyncReg1 <= `BSV_ASSIGNMENT_DELAY ackValue ;// clock domain crossing
              sSyncReg2 <= `BSV_ASSIGNMENT_DELAY sSyncReg1 ;

              // Pulse send
              if ( sEN )
                begin
                   sToggleReg <= `BSV_ASSIGNMENT_DELAY ! sToggleReg ;
                end // if ( sEN )

           end
     end // always @ (posedge sCLK or `BSV_RESET_EDGE sRST)

   always @(posedge dCLK or `BSV_RESET_EDGE sRST)
     begin
        if (sRST == `BSV_RESET_VALUE)
          begin
             dSyncReg1  <= `BSV_ASSIGNMENT_DELAY init;
             dSyncReg2  <= `BSV_ASSIGNMENT_DELAY init;
             dLastState <= `BSV_ASSIGNMENT_DELAY init ;
          end
        else
           begin
              dSyncReg1 <= `BSV_ASSIGNMENT_DELAY sToggleReg ;// domain crossing
              dSyncReg2 <= `BSV_ASSIGNMENT_DELAY dSyncReg1 ;
              dLastState <= `BSV_ASSIGNMENT_DELAY dSyncReg2 ;
           end
     end // always @ (posedge dCLK or `BSV_RESET_EDGE sRST)

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
      begin
         dSyncReg1 = init ;
         dSyncReg2 = init ;
         dLastState = init ;

         sToggleReg = init ;
         sSyncReg1 = ! init ;
         sSyncReg2 = ! init ;

      end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // HandshakeSync
