
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
// dCount and sCount are also delayed and may differ because of latency
// from the synchronization logic
module SyncFIFOLevel(
                     sCLK,
                     sRST,
                     dCLK,
                     sENQ,
                     sD_IN,
                     sFULL_N,
                     dDEQ,
                     dD_OUT,
                     dEMPTY_N,
                     dCOUNT,
                     sCOUNT,
                     sCLR,
                     sCLR_RDY,
                     dCLR,
                     dCLR_RDY
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

   // Counts of capacity  need extra bit to show full, e.g., range is 0 to 32
   output [indxWidth : 0]    dCOUNT;
   output [indxWidth : 0]    sCOUNT;

   // Clear signals on both domains
   input                     sCLR;
   output                    sCLR_RDY;
   input                     dCLR;
   output                    dCLR_RDY;

   // constants for bit masking of the gray code
   wire [indxWidth : 0]      msbset  = ~({(indxWidth + 1){1'b1}} >> 1) ;
   wire [indxWidth - 1 : 0]  msb2set = ~({(indxWidth + 0){1'b1}} >> 1) ;
   wire [indxWidth : 0]      msb12set = msbset | {1'b0, msb2set} ; // 'b11000...

   // FIFO Memory
   reg [dataWidth -1 : 0]    fifoMem [0: depth -1 ] ;
   reg [dataWidth -1 : 0]    dDoutReg ;

   // Enqueue Pointer
   reg [indxWidth : 0]       sGEnqPtr, sBEnqPtr ; // Flops
   reg                       sNotFullReg ;
   wire [indxWidth : 0]      sNextGEnqPtr, sNextBEnqPtr ;
   wire [indxWidth : 0]      sNextCnt, sFutureCnt ;
   wire                      sNextNotFull, sFutureNotFull ;

   // Dequeue Pointer
   reg [indxWidth : 0]       dGDeqPtr, dBDeqPtr ; // Flops
   reg                       dNotEmptyReg ;
   wire [indxWidth : 0]      dNextGDeqPtr, dNextBDeqPtr ;
   wire [indxWidth : 0]      dNextCnt ;
   wire                      dNextNotEmpty;


   // Rgisters needed for capacity counts
   reg [indxWidth  : 0]      sCountReg, dCountReg ;

   // Note for Timing improvement:
   // These signals can be registers to improve a long path from the
   // second stage of the synchronizer to the input of the
   // CountReg.  The path includes a Gray to Binary conversion and a
   // subtraction, which can easily be a long path.
   // The effect is that the count is delayed one additional cycle.
   wire [indxWidth  : 0]     sBDeqPtr,  dBEnqPtr ;

   // flops to sychronize enqueue and dequeue point across domains
   reg [indxWidth : 0]       dSyncReg1, dEnqPtr ;
   reg [indxWidth : 0]       sSyncReg1, sDeqPtr ;

   // Indexes for fifo memory is one bit smaller than indexes
   wire [indxWidth - 1 :0]   sEnqPtrIndx, dDeqPtrIndx ;

   // wires needed for clear processing
   wire                      dRST;
   wire                      sCLRSynced; // dCLR synced to sCLK
   wire                      sCLR_RDY_int;

   wire                      dCLRSynced; // sCLR synced to dCLK
   wire                      dCLR_RDY_int;

   wire                      sClear;
   wire                      dClear;

   // Clear processing requires the use of 2 handshake synchronizers
   SyncHandshake #(.delayreturn(1))
   sClrSync ( .sCLK(sCLK),
              .sRST(sRST),
              .dCLK(dCLK),
              .sEN(sCLR),
              .sRDY(sCLR_RDY_int),
              .dPulse(dCLRSynced));

   SyncHandshake #(.delayreturn(1))
   dClrSync ( .sCLK(dCLK),
              .sRST(sRST),
              .dCLK(sCLK),
              .sEN(dCLR),
              .sRDY(dCLR_RDY_int),
              .dPulse(sCLRSynced));

   // Outputs
   assign                    dD_OUT   = dDoutReg;
   assign                    dEMPTY_N = dNotEmptyReg ;
   assign                    sFULL_N  = sNotFullReg ;
   assign                    sCOUNT = sCountReg;
   assign                    dCOUNT = dCountReg;
   assign                    sCLR_RDY = sCLR_RDY_int;
   assign                    dCLR_RDY = dCLR_RDY_int;

   // Indexes are truncated from the Binary counter
   assign                    sEnqPtrIndx = sBEnqPtr[indxWidth-1:0] ;
   assign                    dDeqPtrIndx = dBDeqPtr[indxWidth-1:0] ;

   // clear signals
   assign                    sClear = sCLR || !sCLR_RDY_int || sCLRSynced;
   assign                    dClear = dCLR || !dCLR_RDY_int || dCLRSynced;
   assign                    dRST = sRST;

   // Fifo memory write
   always @(posedge sCLK)
     begin
        if ( sENQ )
          fifoMem[sEnqPtrIndx] <= `BSV_ASSIGNMENT_DELAY sD_IN ;
     end // always @ (posedge sCLK)

   ////////////////////////////////////////////////////////////////////////
   // Enqueue Pointer and increment logic
   assign sNextBEnqPtr   = sBEnqPtr + 1'b1 ;
   assign sNextGEnqPtr   = sNextBEnqPtr ^ (sNextBEnqPtr >> 1) ;
   assign sNextNotFull   = (sGEnqPtr ^ msb12set) != sDeqPtr ;
   assign sFutureNotFull = (sNextGEnqPtr ^ msb12set) != sDeqPtr ;
   assign sNextCnt       = sBEnqPtr - sBDeqPtr ;
   assign sFutureCnt     = sNextBEnqPtr - sBDeqPtr ;
   assign sBDeqPtr       = grayToBinary( sDeqPtr ) ;


   always @(posedge sCLK or `BSV_RESET_EDGE sRST)
     begin
        if (sRST == `BSV_RESET_VALUE)
          begin
             sBEnqPtr <= `BSV_ASSIGNMENT_DELAY {(indxWidth +1 ) {1'b0}} ;
             sGEnqPtr <= `BSV_ASSIGNMENT_DELAY {(indxWidth +1 ) {1'b0}} ;
             sNotFullReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ; // Mark as full during reset
             sCountReg   <= `BSV_ASSIGNMENT_DELAY {(indxWidth +1 ) {1'b0}} ;
          end // if (sRST == `BSV_RESET_VALUE)
        else
          begin
             if (sClear)
                begin
                   sBEnqPtr <= `BSV_ASSIGNMENT_DELAY {(indxWidth +1 ) {1'b0}} ;
                   sGEnqPtr <= `BSV_ASSIGNMENT_DELAY {(indxWidth +1 ) {1'b0}} ;
                   sNotFullReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
                   sCountReg   <= `BSV_ASSIGNMENT_DELAY {(indxWidth +1 ) {1'b0}} ;
                end
             else if ( sENQ )
               begin
                  sBEnqPtr <= `BSV_ASSIGNMENT_DELAY sNextBEnqPtr ;
                  sGEnqPtr <= `BSV_ASSIGNMENT_DELAY sNextGEnqPtr ;
                  sNotFullReg <= `BSV_ASSIGNMENT_DELAY sFutureNotFull ;
                  sCountReg   <= `BSV_ASSIGNMENT_DELAY sFutureCnt ;
               end
             else
               begin
                  sNotFullReg <= `BSV_ASSIGNMENT_DELAY sNextNotFull ;
                  sCountReg   <= `BSV_ASSIGNMENT_DELAY sNextCnt ;
               end // else: !if( sENQ )
          end // else: !if(sRST == `BSV_RESET_VALUE)
     end // always @ (posedge sCLK or `BSV_RESET_EDGE sRST)

   // Enqueue pointer synchronizer to dCLK
   always @(posedge dCLK  or `BSV_RESET_EDGE sRST)
     begin
        if (sRST == `BSV_RESET_VALUE)
          begin
             dSyncReg1 <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
             dEnqPtr   <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
          end // if (sRST == `BSV_RESET_VALUE)
        else
          begin
             dSyncReg1 <= `BSV_ASSIGNMENT_DELAY sGEnqPtr ; // Clock domain crossing
             dEnqPtr   <= `BSV_ASSIGNMENT_DELAY dSyncReg1 ;
          end // else: !if(sRST == `BSV_RESET_VALUE)
     end // always @ (posedge dCLK  or `BSV_RESET_EDGE sRST)
   ////////////////////////////////////////////////////////////////////////

   ////////////////////////////////////////////////////////////////////////
   // Enqueue Pointer and increment logic
   assign dNextBDeqPtr    = dBDeqPtr + 1'b1 ;
   assign dNextGDeqPtr    = dNextBDeqPtr ^ (dNextBDeqPtr >> 1) ;
   assign dNextNotEmpty   = dGDeqPtr != dEnqPtr ;
   assign dNextCnt        = dBEnqPtr - dBDeqPtr ;
   assign dBEnqPtr        = grayToBinary( dEnqPtr ) ;

   always @(posedge dCLK or `BSV_RESET_EDGE dRST)
     begin
        if (dRST == `BSV_RESET_VALUE)
          begin
             dBDeqPtr     <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
             dGDeqPtr     <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
             dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ; // Mark as empty to avoid dequeues until after reset
             dCountReg    <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
          end // if (sRST == `BSV_RESET_VALUE)
        else
          begin
             if (dClear) begin
                dBDeqPtr     <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
                dGDeqPtr     <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
                dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
                dCountReg    <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
             end
             else if (!dNotEmptyReg && dNextNotEmpty) begin
                dBDeqPtr     <= `BSV_ASSIGNMENT_DELAY dNextBDeqPtr ;
                dGDeqPtr     <= `BSV_ASSIGNMENT_DELAY dNextGDeqPtr ;
                dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b1 ;
                dCountReg    <= `BSV_ASSIGNMENT_DELAY dNextCnt ;
             end
             else if (dDEQ && dNextNotEmpty) begin
                dBDeqPtr     <= `BSV_ASSIGNMENT_DELAY dNextBDeqPtr ;
                dGDeqPtr     <= `BSV_ASSIGNMENT_DELAY dNextGDeqPtr ;
                dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b1 ;
                dCountReg    <= `BSV_ASSIGNMENT_DELAY dNextCnt ;
             end
             else if (dDEQ && !dNextNotEmpty) begin
                dNotEmptyReg <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
                dCountReg    <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
             end
             else begin
                dCountReg    <= `BSV_ASSIGNMENT_DELAY dNextCnt ;
             end
          end // else: !if(sRST == `BSV_RESET_VALUE)
     end // always @ (posedge dCLK or `BSV_RESET_EDGE sRST)

   always @(posedge dCLK `BSV_RESET_EDGE_HEAD)
     begin
`ifdef  BSV_RESET_FIFO_HEAD
        if (dRST == `BSV_RESET_VALUE)
          begin
             dDoutReg     <= `BSV_ASSIGNMENT_DELAY { dataWidth { 1'b0 }} ;
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
              sDeqPtr   <= `BSV_ASSIGNMENT_DELAY {(indxWidth + 1) {1'b0}} ;
           end // if (sRST == `BSV_RESET_VALUE)
         else
           begin
              sSyncReg1 <= `BSV_ASSIGNMENT_DELAY dGDeqPtr ; // clock domain crossing
              sDeqPtr   <= `BSV_ASSIGNMENT_DELAY sSyncReg1 ;
              // sBDeqPtr  <= `BSV_ASSIGNMENT_DELAY grayToBinary( sDeqPtr ) ;
           end // else: !if(sRST == `BSV_RESET_VALUE)
      end // always @ (posedge sCLK  or `BSV_RESET_EDGE sRST)
   ////////////////////////////////////////////////////////////////////////

   // synopsys translate_off
   // Run time assertion check
   always @(posedge sCLK)
     begin
        if ( sENQ && ! sNotFullReg ) $display ("Warning: SyncFIFOLevel: %m -- Enqueing to a full fifo");
     end
   always @(posedge dCLK)
     begin
        if ( dDEQ && ! dNotEmptyReg ) $display ("Warning: SyncFIFOLevel: %m -- Dequeuing from empty fifo");
     end
   // synopsys translate_on

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
        dDoutReg = {((dataWidth + 1)/2){2'b10}} ;

        // initialize the pointer
        sGEnqPtr = {((indxWidth + 1)/2){2'b10}} ;
        sBEnqPtr = sGEnqPtr ;
        sNotFullReg = 1'b0 ;

        dGDeqPtr = sGEnqPtr ;
        dBDeqPtr = sGEnqPtr ;
        dNotEmptyReg = 1'b0;


        // initialize other registers
        sSyncReg1 = sGEnqPtr ;
        sDeqPtr   = sGEnqPtr ;
        dSyncReg1 = sGEnqPtr ;
        dEnqPtr   = sGEnqPtr ;
     end // initial begin
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
          end
        if ( expDepth != depth )
          begin
             ok = 0;
             $display ( "ERROR SyncFiFOLevel.v: index size and depth do not match;" ) ;
             $display ( "\tdepth must equal 2 ** index size. expected %0d", expDepth );
          end

        #0
        if ( ok == 0 ) $finish ;

      end // initial begin
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

   function [indxWidth:0] grayToBinary ;
      input [indxWidth:0] grayin;
      begin: grayToBinary_block
         reg  [indxWidth:0] binary ;
         integer i ;
         for ( i = 0 ; i <= indxWidth ; i = i+1 )
           begin
              binary[i] = ^( grayin >> i ) ;
           end
         grayToBinary = binary ;
      end
   endfunction

endmodule // FIFOSync




`ifdef testBluespec
module testSyncFIFOLevel() ;
   parameter dsize = 8;
   parameter fifodepth = 32;
   parameter fifoidx = 5;

   wire      sCLK,  dCLK, dRST ;
   wire      sENQ, dDEQ;
   wire      sFULL_N, dEMPTY_N ;
   wire [dsize -1:0] sDIN, dDOUT ;

   reg [dsize -1:0]  sCNT, dCNT ;
   reg sRST ;

   wire [fifoidx:0] dItemCnt, sItemCnt ;
   wire             sCLR_RDY;
   wire             dCLR_RDY;
   wire             sCLR;
   wire             dCLR;
   reg [31:0]      count ;
   reg             started ;
   reg             ddeq ;


   ClockGen#(14,15,10)  sc( sCLK );
   ClockGen#(11,12,2600)  dc( dCLK ); // Pause the generation of the destination side clock

   initial
     begin
        sCNT = 0;
        dCNT = 0;
        sRST = `BSV_RESET_VALUE ;
        count = 0;
        started = 0;
        ddeq = 0;

        $display( "running test" ) ;

        $dumpfile("SyncFIFOLevel.vcd");
        $dumpvars(10,testSyncFIFOLevel) ;
        #1
        $dumpon ;
        #200 ;
        sRST = !`BSV_RESET_VALUE ;


        #50000 $finish ;
     end

   SyncFIFOLevel #(dsize,fifodepth,fifoidx)
     dut( sCLK, sRST, dCLK, sENQ, sDIN,
          sFULL_N, dDEQ, dDOUT, dEMPTY_N, dItemCnt, sItemCnt,
          sCLR, sCLR_RDY, dCLR, dCLR_RDY );

   assign sDIN = sCNT ;
   assign sENQ = sFULL_N ;

   assign     dCLR = ((count[7:0] == 8'b0010_0011) && dCLR_RDY);
   assign     sCLR = ((count[7:0] == 8'b0000_0001) && sCLR_RDY);

   always @(posedge sCLK)
     begin
        count <= count + 1 ;
        $display( "scount is %d", sItemCnt ) ;
        if (sENQ )
          begin
             sCNT <= `BSV_ASSIGNMENT_DELAY sCNT + 1;
             $display( "enqueuing is %d", sCNT ) ;
          end // if (sENQ )
      end // always @ (posedge sCLK)

   assign dDEQ = ddeq ;

   always @(dItemCnt or dEMPTY_N or started or count)
      begin
         ddeq = (count > 40) && dEMPTY_N && (started || dItemCnt > 4);
      end // always @ (dItemCnt or dEMPTY_N or started)

   always @(posedge dCLK)
     begin
        $display( "dcount is %d", dItemCnt ) ;
        if (ddeq)
          begin
             started <= 1;
             $display( "dequeing %d", dDOUT ) ;
           end // if (dDEQ )
        else
          begin
             started <= 0;
          end
     end // always @ (posedge dCLK)

endmodule // testSyncFIFO
`endif
