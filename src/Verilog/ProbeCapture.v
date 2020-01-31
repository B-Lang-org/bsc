
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
// REPLICATED CODE WARNING
// If these encodings change, the following files must be kept in sync:
//
// SceMiSerialProbe.bsv
//
// Verilog Probes (ProbeTrigger.v, ProbeCapture.v etc.)
//
// C++ Transactor code (src/lib/SceMi/bsvxactors/SerialProbeXactor.cxx)
//

`define PDISABLED   3'd1
`define PENABLED    3'd2
`define PTRIGGERED  3'd3

`define COLLECTING   2'd0
`define TRIGGERED    2'd1
`define DUMPING      2'd2

module ProbeCapture (
                     UCLK,
                     URST,
                     // Down link
                     CMDEN,
                     CMD,
                     CTIMER,
                     // Up link
                     DELAY,
                     DATAUP,
                     DATAVALID,
                     ACK,
                     //
                     CLK,
                     // Probe data with valid bit
                     PROBEIN,
                     PROBEEN,
                     TRIGGER
                     );

   parameter ProbeId = 0;
   parameter ProbeWidth = 1;
   parameter MemSize  = 32;
   parameter RunLenWidth = 32;

   parameter TriggerToDump = 0;

   parameter MemAddrWidth = 5;

   localparam ProbeWords = (31+ProbeWidth+RunLenWidth)/32;
   localparam ProbeWBits = ((ProbeWidth+RunLenWidth) > 32) ? ProbeWidth+RunLenWidth : 32;
   localparam MemSize1   = MemSize - 1;

   input UCLK;
   input URST;
   input CLK;

   input [ProbeWidth-1:0] PROBEIN;
   input                  PROBEEN;
   input                  TRIGGER;
   input                  CTIMER;

   output [31:0] DATAUP;
   output        DELAY;
   output        DATAVALID;
   input         ACK;

   input         CMDEN;
   input [18:0]  CMD;

   // Output declarations
   wire [31:0]   DATAUP;        // on UCLK
   wire          DELAY;
   wire          DATAVALID;

   wire [15:0] 	probenum = CMD [18:3];
   wire [2:0]   cmd      = CMD  [2:0];

   // On local clock
   reg [ProbeWidth-1:0] probeData; // not reset
   reg                  probeChanged;

   // on UCLK/reset
   reg                     enabled, nextEnabled;
   reg [MemAddrWidth-1:0]  memAddr, nextMemAddr;
   reg [MemAddrWidth-1:0]  sampleCount, nextSampleCount;
   reg [RunLenWidth-1:0]   ctimer, nextCtimer;

   reg [15:0]            ttimer, nextTtimer;
   reg [1:0]             capstate, nextCapstate;

   reg [ProbeWBits-1:0]  dataOut, nextDataOut;  		// not reset
   reg [7:0]             remaining, nextRemaining; 		// not reset
   reg                  captureChanged, nextCaptureChanged; 	// not reset

   // Output definitions
   assign DELAY   = capstate == `DUMPING;
   assign DATAUP    = dataOut[31:0];
   assign DATAVALID = capstate == `DUMPING;

   // Single ported BRAM
   wire [ProbeWidth+RunLenWidth-1:0] memin = {probeData, ctimer};
   wire [ProbeWidth+RunLenWidth-1:0] memdata;
   reg                  memWrite, memEnable;
   BRAM1 #(.PIPELINED(0)
           , .ADDR_WIDTH(MemAddrWidth)
           , .DATA_WIDTH(ProbeWidth+RunLenWidth)
           , .MEMSIZE(MemSize)
           ) captureMemory (.CLK(UCLK)
                            , .EN(memEnable)
                            , .WE(memWrite)
                            , .ADDR(nextMemAddr)
                            , .DI(memin)
                            , .DO(memdata));

   // Local clock -- uclock and lclock are edge aligned.
   always @(posedge CLK) begin
      if (PROBEEN && enabled && probeData != PROBEIN) begin
         probeData    <= `BSV_ASSIGNMENT_DELAY PROBEIN;
         probeChanged <= `BSV_ASSIGNMENT_DELAY ! probeChanged;
      end
   end

   always @(posedge UCLK) begin
      if (URST != !`BSV_RESET_VALUE) begin
         enabled     <= `BSV_ASSIGNMENT_DELAY 1'b0;
         capstate    <= `BSV_ASSIGNMENT_DELAY `COLLECTING;
         memAddr     <= `BSV_ASSIGNMENT_DELAY { MemAddrWidth {1'b0 }};
         sampleCount <= `BSV_ASSIGNMENT_DELAY { {MemAddrWidth-1 {1'b0 }}, 1'b1 };
         ctimer      <= `BSV_ASSIGNMENT_DELAY { RunLenWidth {1'b1 }};
         ttimer      <= `BSV_ASSIGNMENT_DELAY 16'h0;
      end
      else begin
         enabled     <= `BSV_ASSIGNMENT_DELAY nextEnabled;
         capstate    <= `BSV_ASSIGNMENT_DELAY nextCapstate;
         memAddr     <= `BSV_ASSIGNMENT_DELAY nextMemAddr;
         sampleCount <= `BSV_ASSIGNMENT_DELAY nextSampleCount;
         ctimer      <= `BSV_ASSIGNMENT_DELAY nextCtimer;
         ttimer      <= `BSV_ASSIGNMENT_DELAY nextTtimer;
      end // else: !if(URST != !`BSV_RESET_VALUE)

      captureChanged <= `BSV_ASSIGNMENT_DELAY nextCaptureChanged;
      remaining      <= `BSV_ASSIGNMENT_DELAY nextRemaining;
      dataOut        <= `BSV_ASSIGNMENT_DELAY nextDataOut;
   end

   always @(enabled  or capstate or memAddr or sampleCount or ctimer or ttimer or
            captureChanged or remaining or dataOut or
            CTIMER or TRIGGER  or
            probeChanged or ACK or CMDEN or cmd or probenum or memdata
            ) begin :combo

      reg [ProbeWBits+31:0]  temp;
      reg [MemAddrWidth-1:0] incrSampleCount;
      reg                    externalTrigger;
      reg                    saveNow;
      reg [15:0]             wordsToSend;

      temp              = {32'b0,dataOut};
      incrSampleCount   = (sampleCount != MemSize1[MemAddrWidth-1:0]) ? sampleCount + 1'b1 : sampleCount;
      externalTrigger   = CMDEN && (probenum == ProbeId[15:0]) && (cmd == `PTRIGGERED);
      saveNow           = (probeChanged != captureChanged) || (ctimer == {RunLenWidth {1'b1}});
      wordsToSend       = ProbeWords[15:0] * sampleCount;

      nextEnabled               = enabled;
      nextCapstate              = capstate;
      nextMemAddr               = memAddr;
      nextSampleCount           = sampleCount;
      nextCtimer                = ctimer;
      nextTtimer                = ttimer;

      nextCaptureChanged 	= captureChanged;
      nextRemaining 		= remaining;
      nextDataOut   		= dataOut;

      memWrite 		        = 1'b0;
      memEnable                 = 1'b0;

      if ((capstate == `COLLECTING) && enabled) begin
         if (CTIMER && saveNow) begin
            memWrite             = 1'b1;
            memEnable            = 1'b1;
            nextCtimer           = 'b0;
            nextMemAddr          = (memAddr == MemSize1[MemAddrWidth-1:0]) ? {MemAddrWidth {1'b0}} : memAddr + 1'b1;
            nextSampleCount      = incrSampleCount ;
            nextCaptureChanged   = probeChanged;
         end
         else if (CTIMER) begin
            nextCtimer = ctimer + 1'b1;
         end

         if ((CTIMER && TRIGGER) || externalTrigger) begin
            nextCapstate =  `TRIGGERED;
         end
      end // if (capstate == `COLLECTING && enabled)

      else if ((capstate == `TRIGGERED) && CTIMER) begin
         if (ttimer == 'b0) begin
            memWrite             = 1'b1;
            memEnable            = 1'b1;
            nextCtimer           = { RunLenWidth {1'b1}};
            nextMemAddr          = (memAddr == MemSize1[MemAddrWidth-1:0]) ? {MemAddrWidth {1'b0}} : memAddr + 1'b1;
            nextCaptureChanged   = probeChanged;

            nextRemaining        = 8'b0;
            nextCapstate         = `DUMPING;

            nextDataOut[31:0]        = {ProbeId[15:0], wordsToSend};
            nextTtimer           = TriggerToDump [15:0];
         end
         else if (saveNow) begin
            memWrite = 1'b1;
            memEnable = 1'b1;

            nextCtimer          = 'b0;
            nextMemAddr         = (memAddr == MemSize1[MemAddrWidth-1:0]) ? {MemAddrWidth {1'b0}} : memAddr + 1'b1;
            nextSampleCount     = incrSampleCount;
            nextCaptureChanged  = probeChanged;
            nextTtimer          = ttimer - 1'b1;
         end
         else begin
            nextCtimer = ctimer + 1'b1;
            nextTtimer = ttimer - 1'b1;
         end
      end // if ((capstate == `TRIGGERED) && CTIMER)

      else if ((capstate == `DUMPING) && ACK) begin
         if (remaining == 8'b0 && sampleCount != 'b0) begin
            memEnable = 1'b1;
            nextSampleCount = sampleCount - 1'b1;
            nextRemaining   = ProbeWords[7:0] - 1'b1;
            nextDataOut     = memdata;
            nextMemAddr     = (memAddr == 'b0) ? MemSize1[MemAddrWidth-1:0] : memAddr - 1'b1;
         end
         else if (remaining != 8'b0) begin
            nextDataOut      = temp[ProbeWBits+31:32];
            nextRemaining    = remaining - 1'b1;
         end
         else if (remaining == 8'b0 && sampleCount == 'b0) begin
            nextCapstate     = `COLLECTING;
            nextSampleCount  = { {MemAddrWidth-1 {1'b0 }}, 1'b1 };
            nextCtimer       = { RunLenWidth {1'b1}}; // TRIGGER collect in next cycle
         end
      end // if ((capstate == `DUMPING) && ACK)

      // Enable or disable the probe
      if (CMDEN && (probenum == ProbeId[15:0])) begin
         if (cmd == `PENABLED) begin
            nextEnabled = 1'b1;
         end
         else if (cmd == `PDISABLED) begin
            nextEnabled =  1'b0;
         end
      end
      if (!enabled && capstate == `COLLECTING) begin
         nextSampleCount = { {MemAddrWidth-1 {1'b0 }}, 1'b1 };
         nextCtimer      = { RunLenWidth {1'b1}}; // TRIGGER collect in next cycle
      end
   end



`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      enabled     <= 1'b0 ;
      capstate    <= 2'b0 ;
      memAddr     <= { MemAddrWidth/2 {2'b10}};
      sampleCount <= { MemAddrWidth/2 {2'b10}};
      ctimer      <= { RunLenWidth/2 {2'b10}};
      ttimer      <= { 16'haaaa };

      captureChanged <= 1'b0;
      remaining   <= 8'haa ;
      dataOut      <= { (ProbeWBits/2) {2'b10 } };

      probeData   <= { ProbeWidth {1'b0 } };
      probeChanged <= 1'b0;
   end
   // synopsys translate_on
`endif

endmodule
