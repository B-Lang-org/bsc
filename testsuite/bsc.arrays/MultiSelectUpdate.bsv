
(* synthesize *)
module sysMultiSelectUpdate ();

  
  rule doDisp (True);
  
    int arr[5][5];
  
    for (Integer x = 0; x < 5; x = x + 1)
      for (Integer y = 0; y < 5; y = y + 1)
        arr[x][y] = fromInteger(x - y);
    
    for (Integer x = 0; x < 5; x = x + 1)
      for (Integer y = 0; y < 5; y = y + 1)
        $display("arr[%0d][%0d]: %0d", fromInteger(x), fromInteger(y), arr[x][y]);
	 
    for (Integer x = 0; x < 5; x = x + 1)
      for (Integer y = 0; y < 5; y = y + 1)
        arr[x][y] = arr[y][x];

    $display("-----------------------------------");

    for (Integer x = 0; x < 5; x = x + 1)
      for (Integer y = 0; y < 5; y = y + 1)
        $display("arr[%0d][%0d]: %0d", fromInteger(x), fromInteger(y), arr[x][y]);
	 
  endrule
  
endmodule
