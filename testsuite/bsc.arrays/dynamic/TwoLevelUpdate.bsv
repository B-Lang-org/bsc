// Test updating a vector based on a dynamic index
// that is the result of a dynamic selection
(* synthesize *)
module sysTwoLevelUpdate();

  int arr[4] = {1, 2, 3, 4};
  int indices[4] = {0, 3, 2, 1};

  Reg#(UInt#(3)) j <- mkReg(0);

  arr[indices[j]] = 0;

  rule test;
    $display("{%0d,%0d,%0d,%0d}", arr[0], arr[1], arr[2], arr[3]);
    if (j == 3) $finish(0);
    j <= j + 1;
  endrule

endmodule

