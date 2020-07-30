(* synthesize *)
module sysUninitBitOK2();
  Bit#(5) x;

  for(Integer i = 1; i < 4; i = i + 1)
    x[i] = 1;
  
  rule test;
    for(Integer j = 1; j < 4; j = j + 1)
       $display("x[%0d] = %0d", j, x[j]);
    $finish(0);
  endrule

endmodule
   
