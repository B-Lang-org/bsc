(* synthesize *)
module sysRealDisplay();
   Real r = 2990.754;
   
   rule test;
      $display("Decimal format: %f", r);
      $display("Truncated decimal #1: %1.1f", r);
      $display("Truncated decumal #2: %1.2f", r);
      $finish(0);
   endrule
   
endmodule
