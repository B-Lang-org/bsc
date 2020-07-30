(* synthesize *)
module sysZeroUnsignedDisplay();

  UInt#(0) x = 0;
  
  rule test;
     $display("Test: ", x);
     $finish(0);
  endrule

endmodule

