(* synthesize *)
module sysUninitBitOK3();
  Bit#(5) x;

  for(Integer i = 1; i < 4; i = i + 1)
    x[i] = 1;
  
  rule test;
    $display("x[3:2] = %0d", x[3:2]);
    $finish(0);
  endrule

endmodule
   
