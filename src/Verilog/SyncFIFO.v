
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

`ifdef BSV_RESET_FIFO_HEAD
 `define BSV_RESET_EDGE_HEAD or `BSV_RESET_EDGE dRST
`else
 `define BSV_RESET_EDGE_HEAD
`endif


// A clock synchronization FIFO where the enqueue and dequeue sides are in
// different clock domains.
// There are no restrictions w.r.t. clock frequencies
// The depth of the FIFO must be a power of 2 (2,4,8,...) since the
// indexing uses a Gray code counter.
// FULL and EMPTY signal are pessimistic, that is, they are asserted
// immediately when the FIFO becomes FULL or EMPTY, but their deassertion
// is delayed due to synchronization latency.
module SyncFIFO(
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
   parameter                 depth = 2 ; // minimum 2
   parameter                 indxWidth = 1 ; // minimum 1

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

   // constants for bit masking of the gray code
   wire [indxWidth : 0]      msbset  = ~({(indxWidth + 1){1'b1}} >> 1) ;
   wire [indxWidth - 1 : 0]  msb2set = ~({(indxWidth + 0){1'b1}} >> 1) ;
   wire [indxWidth : 0]      msb12set = msbset | {1'b0, msb2set} ; // 'b11000...

   // FIFO Memory
   reg [dataWidth -1 : 0]    fifoMem [0: depth -1 ] ;
   reg [dataWidth -1 : 0]    dDoutReg ;

   // Enqueue Pointer support
   reg [indxWidth +1 : 0]    sGEnqPtr, sGEnqPtr1 ; // Flops
   reg                       sNotFullReg ;
   wire                      sNextNotFull, sFutureNotFull ;

   // Dequeue Pointer support
   reg [indxWidth+1 : 0]       dGDeqPtr, dGDeqPtr1 ; // Flops
   reg                       dNotEmptyReg ;
   wire                      dNextNotEmpty;

   // Reset generation
   wire                      dRST ;

   // flops to sychronize enqueue and dequeue point across domains
   reg [indxWidth : 0]       dSyncReg1, dEnqPtr ;
   reg [indxWidth : 0]       sSyncReg1, sDeqPtr ;

   wire [indxWidth - 1 :0]   sEnqPtrIndx, dDeqPtrIndx ;

   // Resets
   assign                    dRST = sRST ;

   // Outputs
   assign                    dD_OUT   = dDoutReg     ;
   assign                    dEMPTY_N = dNotEmptyReg ;
   assign                    sFULL_N  = sNotFullReg  ;

   // Indexes are truncated from the Gray counter with parity
   assign                    sEnqPtrIndx  = sGEnqPtr[indxWidth-1:0];
   assign                    dDeqPtrIndx  = dGDeqPtr[indxWidth-1:0];

   // Fifo memory write
   always @(posedge sCLK)
     begin
        if ( sENQ )
          fifoMem[sEnqPtrIndx] <= `BSV_ASSIGNMENT_DELAY sD_IN ;
     end // always @ (posedge sCLK)

   ////////////////////////////////////////////////////////////////////////
   // Enqueue Pointer and increment logic
   assign sNextNotFull   = (sGEnqPtr [indxWidth+1:1] ^ msb12set) != sDeqPtr ;
   assign sFutureNotFull = (sGEnqPtr1[indxWidth+1:1] ^ msb12set) != sDeqPtr ;

   always @(posedge sCLK or `BSV_RESET_EDGE sRST)
     begin
        if (sRST == `BSV_RESET_VALUE)
          begin
             sGEnqPtr    <= `BSV_ASSIGNMENT_DELAY {(indxWidth +2 ) {1'b0}} ;
             sGEnqPtr1   <= `BSV_ASSIGNMENT_DELAY { {indxWidth {1'b0}}, 2'b11} ;
             sNotFullReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ; // Mark as full during reset to avoid spurious loads
          end // if (sRST == `BSV_RESET_VALUE)
        else
           begin
              if ( sENQ )
                begin
                   sGEnqPtr1   <= `BSV_ASSIGNMENT_DELAY incrGrayP( sGEnqPtr1 ) ;
                   sGEnqPtr    <= `BSV_ASSIGNMENT_DELAY sGEnqPtr1 ;
                   sNotFullReg <= `BSV_ASSIGNMENT_DELAY sFutureNotFull ;
                end // if ( sENQ )
              else
                begin
                   sNotFullReg <= `BSV_ASSIGNMENT_DELAY  sNextNotFull ;
                end // else: !if( sENQ )
           end // else: !if(sRST == `BSV_RESET_VALUE)
     end // always @ (posedge sCLK or `BSV_RESET_EDGE sRST)


   // Enqueue pointer synchronizer to dCLK
   always @(posedge dCLK  or `BSV_RESET_EDGE dRST)
     begin
        if (dRST == `BSV_RESET_VALUE)
          begin
             dSyncReg1 <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
             dEnqPtr   <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
          end // if (dRST == `BSV_RESET_VALUE)
        else
          begin
             dSyncReg1 <= `BSV_ASSIGNMENT_DELAY sGEnqPtr[indxWidth+1:1] ; // Clock domain crossing
             dEnqPtr   <= `BSV_ASSIGNMENT_DELAY dSyncReg1 ;
          end // else: !if(dRST == `BSV_RESET_VALUE)
     end // always @ (posedge dCLK  or `BSV_RESET_EDGE dRST)
   ////////////////////////////////////////////////////////////////////////


   ////////////////////////////////////////////////////////////////////////
   // Enqueue Pointer and increment logic
   assign dNextNotEmpty   = dGDeqPtr[indxWidth+1:1]  != dEnqPtr ;

   always @(posedge dCLK or `BSV_RESET_EDGE dRST)
     begin
        if (dRST == `BSV_RESET_VALUE)
          begin
             dGDeqPtr     <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 2) {1'b0}} ;
             dGDeqPtr1    <= `BSV_ASSIGNMENT_DELAY {{indxWidth {1'b0}}, 2'b11 } ;
             dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
          end // if (dRST == `BSV_RESET_VALUE)
        else
           begin
              if ((!dNotEmptyReg || dDEQ) && dNextNotEmpty) begin
                 dGDeqPtr     <= `BSV_ASSIGNMENT_DELAY dGDeqPtr1 ;
                 dGDeqPtr1    <= `BSV_ASSIGNMENT_DELAY incrGrayP( dGDeqPtr1 );
                 dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b1;
              end
              else if (dDEQ && !dNextNotEmpty) begin
                 dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b0;
              end
           end // else: !if(dRST == `BSV_RESET_VALUE)
     end // always @ (posedge dCLK or `BSV_RESET_EDGE dRST)


   always @(posedge dCLK `BSV_RESET_EDGE_HEAD)
     begin
`ifdef  BSV_RESET_FIFO_HEAD
        if (dRST == `BSV_RESET_VALUE)
          begin
             dDoutReg    <= `BSV_ASSIGNMENT_DELAY {dataWidth {1'b0}} ;
          end // if (dRST == `BSV_RESET_VALUE)
        else
`endif
          begin
             if ((!dNotEmptyReg || dDEQ) && dNextNotEmpty) begin
                dDoutReg     <= `BSV_ASSIGNMENT_DELAY fifoMem[dDeqPtrIndx] ;
             end
          end
     end

    // Dequeue pointer synchronized to sCLK
    always @(posedge sCLK  or `BSV_RESET_EDGE sRST)
      begin
         if (sRST == `BSV_RESET_VALUE)
           begin
              sSyncReg1 <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
              sDeqPtr   <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ; // When reset mark as not empty
           end // if (sRST == `BSV_RESET_VALUE)
         else
           begin
              sSyncReg1 <= `BSV_ASSIGNMENT_DELAY dGDeqPtr[indxWidth+1:1] ; // clock domain crossing
              sDeqPtr   <= `BSV_ASSIGNMENT_DELAY sSyncReg1 ;
           end // else: !if(sRST == `BSV_RESET_VALUE)
      end // always @ (posedge sCLK  or `BSV_RESET_EDGE sRST)
   ////////////////////////////////////////////////////////////////////////

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin : initBlock
        integer i ;

        // initialize the FIFO memory with aa's
        for (i = 0; i < depth; i = i + 1)
          begin
             fifoMem[i] = {((dataWidth + 1)/2){2'b10}} ;
          end
        dDoutReg     = {((dataWidth + 1)/2){2'b10}} ;

        // initialize the pointer
        sGEnqPtr = {((indxWidth + 2)/2){2'b10}} ;
        sGEnqPtr1 = sGEnqPtr ;
        sNotFullReg = 1'b0 ;

        dGDeqPtr = sGEnqPtr ;
        dGDeqPtr1 = sGEnqPtr ;
        dNotEmptyReg = 1'b0;


        // initialize other registers
        sSyncReg1 = sGEnqPtr ;
        sDeqPtr   = sGEnqPtr ;
        dSyncReg1 = sGEnqPtr ;
        dEnqPtr   = sGEnqPtr ;
     end // block: initBlock
   // synopsys translate_on



   // synopsys translate_off
   initial
     begin : parameter_assertions
        integer ok ;
        integer i, expDepth ;

        ok = 1;
        expDepth = 1 ;

        // calculate x = 2 ** (indxWidth - 1)
        for( i = 0 ; i < indxWidth ; i = i + 1 )
          begin
             expDepth = expDepth * 2 ;
          end // for ( i = 0 ; i < indxWidth ; i = i + 1 )

        if ( expDepth != depth )
          begin
             ok = 0;
             $display ( "ERROR SyncFiFO.v: index size and depth do not match;" ) ;
             $display ( "\tdepth must equal 2 ** index size. expected %0d", expDepth );
          end

        #0
        if ( ok == 0 ) $finish ;

      end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

   function [indxWidth+1:0] incrGrayP ;
      input [indxWidth+1:0] grayPin;

      begin: incrGrayPBlock
         reg [indxWidth :0] g;
         reg                p ;
         reg [indxWidth :0] i;

         g = grayPin[indxWidth+1:1];
         p = grayPin[0];
         i = incrGray (g,p);
         incrGrayP = {i,~p};
      end
   endfunction
   function [indxWidth:0] incrGray ;
      input [indxWidth:0] grayin;
      input parity ;

      begin: incrGrayBlock
         integer               i;
         reg [indxWidth: 0]    tempshift;
         reg [indxWidth: 0]    flips;

         flips[0] = ! parity ;
         for ( i = 1 ; i < indxWidth ; i = i+1 )
           begin
              tempshift = grayin << (2 + indxWidth - i ) ;
              flips[i]  = parity & grayin[i-1] & ~(| tempshift ) ;
           end
         tempshift = grayin << 2 ;
         flips[indxWidth] = parity & ~(| tempshift ) ;

         incrGray = flips ^ grayin ;
      end
   endfunction

endmodule // FIFOSync


`ifdef testBluespec
module testSyncFIFO() ;
   parameter dsize = 8;
   parameter fifodepth = 32;
   parameter fifoidx = 5;

   wire      sCLK,  dCLK, dRST ;
   wire      sENQ, dDEQ;
   wire      sFULL_N, dEMPTY_N ;
   wire [dsize -1:0] sDIN, dDOUT ;

   reg [dsize -1:0]  sCNT, dCNT ;
   reg sRST, sCLR ;

   ClockGen#(15,14,10)  sc( sCLK );
   ClockGen#(11,12,2600)  dc( dCLK );

   initial
     begin
        sCNT = 0;
        dCNT = 0;
        sCLR = 1'b0 ;

        sRST = `BSV_RESET_VALUE ;
        $display( "running test" ) ;

        $dumpfile("SyncFIFO.vcd");
        $dumpvars(5,testSyncFIFO) ;
        $dumpon ;
        #200 ;
        sRST = !`BSV_RESET_VALUE ;


        #100000 $finish ;
     end // initial begin
   initial
     begin
        #50000 ;
        @(posedge sCLK ) ;
        sCLR <= `BSV_ASSIGNMENT_DELAY 1'b1 ;
        @(posedge sCLK ) ;
        sCLR <= `BSV_ASSIGNMENT_DELAY 1'b0 ;

      end

   SyncFIFO #(dsize,fifodepth,fifoidx)
     dut( sCLK, sRST, dCLK, sENQ, sDIN,
          sFULL_N, // sCLR,
          dDEQ, dDOUT, dEMPTY_N );

   assign sDIN = sCNT ;
   assign sENQ = sFULL_N ;


   always @(posedge sCLK)
     begin
        if (sENQ )
          begin
             sCNT <= `BSV_ASSIGNMENT_DELAY sCNT + 1;
          end
      end // always @ (posedge sCLK)

   assign dDEQ = dEMPTY_N ;

   always @(posedge dCLK)
     begin
        if (dDEQ )
           begin
              $display( "dequeing %d", dDOUT ) ;
           end
     end // always @ (posedge dCLK)

endmodule // testSyncFIFO
`endif
