
(* synthesize *)
module sysSelectUpdate ();

  
  rule doDisp (True);
  
    int arr[5] = {1,2,3,4,5};
  
    for (Integer x = 0; x < 5; x = x + 1)
      $display("Arr %0d: %0d", fromInteger(x), arr[x]);
  
    arr[3] = 177;

    for (Integer x = 0; x < 5; x = x + 1)
      $display("Arr %0d: %0d", fromInteger(x), arr[x]);
      
    for (Integer x = 0; x < 5; x = x + 1)
      arr[x] = arr[x] + 17;
      
    for (Integer x = 0; x < 5; x = x + 1)
      $display("Arr %0d: %0d", fromInteger(x), arr[x]);
  endrule
  
endmodule
