(* synthesize *)
module sysUpdateArrayUndefinedIndex();

  int arr[4] = {1, 2, 3, 4};

  arr[?] = 0;

  rule test;
    $display(arr[0]);
  endrule
 
endmodule