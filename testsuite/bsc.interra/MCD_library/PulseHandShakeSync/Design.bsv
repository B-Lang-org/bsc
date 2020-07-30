//Testcase for clock domain crossing using Pulse handshaked synchronizer : MCD

import Clocks::*;

interface Design_IFC;
 method Action stop();
 method UInt#(16) sent();
 method UInt#(16) recvd();
endinterface : Design_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkDesign#(Clock src_clk, Reset src_rst) (Design_IFC);

  // Boolean flag controls whether pulses are sent through the synchronizer
  Reg#(Bool) run <- mkReg(True, clocked_by src_clk, reset_by src_rst);

  // Counters which count number of pulses sent and received
  Reg#(UInt#(16)) num_sent  <- mkReg(0, clocked_by src_clk, reset_by src_rst);
  Reg#(UInt#(16)) num_recvd <- mkReg(0);

  // The pulse synchronizer being tested
  SyncPulseIfc sync <- mkSyncHandshakeToCC(src_clk, src_rst);

  // This pulseWire allows the sender rule (which must run before the
  // stop method) to communicate to the send_counter rule (which must
  // run after the sent method), so that sent and stop can be called
  // from the same rule externally.
  PulseWire sentPulse <- mkPulseWire(clocked_by src_clk, reset_by src_rst);

  rule sender (run);
    sync.send();
    sentPulse.send();
  endrule
  
  rule send_counter (sentPulse);
    num_sent <= num_sent + 1;
    $display("Sent pulse at %t", $time);
  endrule

  rule receiver (sync.pulse);
    num_recvd <= num_recvd + 1;
    $display("Received pulse at %t", $time);
  endrule
    
  method Action stop();
    run <= False;
  endmethod

  method UInt#(16) sent();
    return num_sent;
  endmethod

  method UInt#(16) recvd();
    return num_recvd;
  endmethod

endmodule
