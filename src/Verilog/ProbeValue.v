
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


`define PENABLE   3'd2
`define PSENDONCE 3'd5 // must agree with EnableMode in SceMiSerialProbe

module ProbeValue (
                   UCLK,
                   URST,
                   // Down link
                   CMDEN,
                   CMD,
                   // Up link
                   DELAY,
                   DATAUP,
                   DATAVALID,
                   ACK,
                   //
                   CLK,
                   // Probe data with valid bit
                   PROBEIN,
                   PROBEEN
                 );

   parameter ProbeId = 0;
   parameter ProbeWidth = 1;
   parameter InitiallyEnabled = 1'b0;

   localparam ProbeWords = (31+ProbeWidth)/32;
   localparam ProbeWBits = (ProbeWidth > 32) ? ProbeWidth : 32;

   input UCLK;
   input URST;
   input CLK;

   input [ProbeWidth-1:0] PROBEIN;
   input                  PROBEEN;

   output [31:0] DATAUP;
   output        DELAY;
   output        DATAVALID;
   input         ACK;

   input         CMDEN;
   input [18:0]  CMD;

   // Output declarations
   reg [31:0]    DATAUP;        // on UCLK
   wire          DELAY;

   wire [15:0]  probenum = CMD [18:3];
   wire [2:0]   cmd      = CMD  [2:0];

   // On local clock
   reg [ProbeWidth-1:0] probeData; // not reset
   reg                  probeChanged;

   // on UCLK/reset
   reg                  enabled;
   reg                  sending;
   reg                  forced;
   reg 			sendOnce;
   reg 			sentOne;
   reg [7:0]            remaining;
   reg [ProbeWBits-1:0] captured; // not reset
   reg                  captureChanged;

   wire newData     = probeChanged != captureChanged;
   assign DELAY   = enabled && newData;
   assign DATAVALID = sending;
   wire [ProbeWBits+31:0]  temp = {32'b0,captured};

   always @(posedge UCLK) begin
      if (URST != !`BSV_RESET_VALUE) begin
         enabled   <= `BSV_ASSIGNMENT_DELAY InitiallyEnabled;
	 forced    <= `BSV_ASSIGNMENT_DELAY 1'b0;
         remaining <= `BSV_ASSIGNMENT_DELAY 8'b0;
         sending   <= `BSV_ASSIGNMENT_DELAY 1'b0;
         sendOnce  <= `BSV_ASSIGNMENT_DELAY 1'b0;
         sentOne   <= `BSV_ASSIGNMENT_DELAY 1'b0;
      end
      else begin
         // Enable or disable the probe
         if (CMDEN && (probenum == ProbeId[15:0])) begin
            enabled <= `BSV_ASSIGNMENT_DELAY (cmd == `PENABLE || cmd == `PSENDONCE);
            forced  <= `BSV_ASSIGNMENT_DELAY (cmd == `PENABLE);
            sendOnce<= `BSV_ASSIGNMENT_DELAY (cmd == `PSENDONCE);
            sentOne <= `BSV_ASSIGNMENT_DELAY 1'b0;
         end
         else begin
            forced  <= `BSV_ASSIGNMENT_DELAY 1'b0 ;
         end

         // FSM for shipping out data
         if ((enabled!=sentOne) &&  !sending && (newData || forced)) begin
            remaining <= `BSV_ASSIGNMENT_DELAY ProbeWords[7:0];
            captured  <= `BSV_ASSIGNMENT_DELAY probeData;
            DATAUP    <= `BSV_ASSIGNMENT_DELAY  {ProbeId[15:0], 8'b0, ProbeWords[7:0] };
            sending   <= `BSV_ASSIGNMENT_DELAY  1'b1;
            sentOne   <= `BSV_ASSIGNMENT_DELAY  sendOnce;
         end
         else if (ACK && sending && remaining != 16'b0) begin
            remaining  <= `BSV_ASSIGNMENT_DELAY remaining - 1'd1;
            DATAUP     <= `BSV_ASSIGNMENT_DELAY captured [31:0];
            captured   <= `BSV_ASSIGNMENT_DELAY temp[ProbeWBits+31:32];
         end
         else if (ACK && sending && remaining == 8'b0) begin
            sending        <= `BSV_ASSIGNMENT_DELAY 1'b0;
            captureChanged <= `BSV_ASSIGNMENT_DELAY probeChanged;
         end
      end
   end

   // Local clock == uclock and lclock are edge aligned.
   wire newProbeData = probeData != PROBEIN;
   always @(posedge CLK) begin
      if (PROBEEN && newProbeData) begin
         probeData    <= `BSV_ASSIGNMENT_DELAY PROBEIN;
         probeChanged <= `BSV_ASSIGNMENT_DELAY ! probeChanged;
      end
      // synopsys translate_off
      if (enabled && newProbeData && newData) begin
         $display ("Error: %m Probevalue has been overrun with data!");
      end
      // synopsys translate_on

   end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      probeData   <= { ProbeWidth {1'b0 } };
      probeChanged <= 1'b0;

      enabled     <= 1'b0 ;
      sending     <= 1'b0 ;
      forced      <= 1'b0;
      remaining   <= 8'h0 ;
      captured    <= { ProbeWBits/2 {2'b10 } };
      captureChanged <= 1'b0;
      DATAUP      <= {16 {2'b10}};
   end
   // synopsys translate_on
`endif

endmodule
