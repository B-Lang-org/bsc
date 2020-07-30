// test sugar for displaying time in BSV

module sysDisplayTime(Empty);
   // have a register with reset, to avoid the rule firing during reset
   Reg#(Bool) start <- mkReg(True);

   rule only (start);
      $display("Time: %t", $time);
      $finish(0);
   endrule: only
endmodule: sysDisplayTime

