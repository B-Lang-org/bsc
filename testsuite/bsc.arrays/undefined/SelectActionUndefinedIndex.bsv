(* synthesize *)
module sysSelectActionUndefinedIndex();

  Action arr[4] = {$display(1), $display(2), $display(3), $display(4)};

  rule test;
    arr[?];
  endrule
 
endmodule