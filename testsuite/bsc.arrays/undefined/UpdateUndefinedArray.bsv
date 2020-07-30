(* synthesize *)
module sysUpdateUndefinedArray();

  int arr[4] = ?;

  for(Integer i = 0; i < 4; i = i + 1)
    arr[i] = fromInteger(i);

  rule test;
    $display(arr[0]);
  endrule
 
endmodule