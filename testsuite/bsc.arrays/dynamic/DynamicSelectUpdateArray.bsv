// Test updating an array based on a dynamic index
// that is the result of a dynamic selection
(* synthesize *)
module sysDynamicSelectUpdateArray();

  int temp[4] = {?, ?, ?, ?};
  
  int arrs[4][4] = {temp, temp, temp, temp};

  for(int i = 0; i < 4; i = i + 1)
    for(int j = 0; j < 4; j = j + 1)
      arrs[i][j] = -i - j - 1;

  Reg#(UInt#(3)) j <- mkReg(0);

  let arr = arrs[j];
  arr[2] = 0;

  rule test;
    $display("{%0d,%0d,%0d,%0d}", arr[0], arr[1], arr[2], arr[3]);
    if (j == 3) $finish(0);
    j <= j + 1;
  endrule

endmodule

