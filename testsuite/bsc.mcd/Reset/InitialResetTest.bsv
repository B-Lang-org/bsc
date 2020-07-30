import Clocks::*;

(* synthesize *)
module sysInitialResetTest ();

   Reset r <- mkInitialReset(5);

   Reg#(Bool) done <- mkReg(False, reset_by r);

   // This is just to introduce RST_N to the r_display rule
   // to avoid the Verilog system-task-on-negedge issue.
   Reg#(Bool) toggle <- mkReg(False);

   rule r_display;
      $display ("tick!");
      toggle <= !toggle;
   endrule

   rule r_done (!done);
      done <= True;
      $display ("done!");
   endrule

   rule r_finish (done);
      $finish(0);
   endrule

endmodule


