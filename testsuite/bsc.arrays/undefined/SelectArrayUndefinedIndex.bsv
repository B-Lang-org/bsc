(* synthesize *)
module sysSelectArrayUndefinedIndex();

  Integer arr[4] = {1, 2, 3, 4};

  rule test;
    $display("%0d", arr[?]);
    $finish(0);
  endrule
 
endmodule