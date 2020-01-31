
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


module ProbeHook (
                  .UCLK(uclk),
                  .URST(urst),
                  .ACK(ack),
                  .DATAUP(data),
                  .DATAVALID(dataValid),
                  .DELAY(delay),
                  .CMDEN(cmden),
                  .CMD(probenum_cmd),
                  .CTIMER(ctimer)
                  );
   input uclk;
   input urst;
   input ack;

   output [31:0] data;
   wire [31:0]   data;

   output        dataValid;
   wire          dataValid;

   output        delay;
   wire          delay = 1'b0;

   input         cmden;
   input [18:0]  probenum_cmd;
   input         ctimer;

   assign data = 32'b0;
   assign dataValid = 1'b0;

   // This module does not do anything.  It only leaves a crumb
   // for other tools to connect to these signals.
   // The output signals are passive
endmodule
