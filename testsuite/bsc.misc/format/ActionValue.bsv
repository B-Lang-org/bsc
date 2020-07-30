// Test for Bug 1554

(* synthesize *)
module sysActionValue();

   rule rl;
      Fmt f1 = $format("%t", $time);
      $display(f1);
   endrule

endmodule

