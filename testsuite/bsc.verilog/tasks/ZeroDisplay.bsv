(* synthesize *)
module sysZeroDisplay();

  Bit#(0) x = 0;
  
  Bit#(8) y = 237;

  rule test;
     $display("Test: %h", y, x);
     $finish(0);
  endrule

endmodule

