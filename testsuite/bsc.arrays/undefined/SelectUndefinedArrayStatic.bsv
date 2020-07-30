(* synthesize *)
module sysSelectUndefinedArrayStatic();
  
  Int#(16) arr[4] = ?;

  rule test;
    $display("%0d", arr[1]);
    $finish(0);
  endrule

endmodule
