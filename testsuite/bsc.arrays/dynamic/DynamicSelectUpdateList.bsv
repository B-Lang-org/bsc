import List::*;
// Test updating a list based on a dynamic index
// that is the result of a dynamic selection
(* synthesize *)
module sysDynamicSelectUpdateList();

  List#(List#(Integer)) ls = replicate(4, replicate(4, ?));
  for(Integer i = 0; i < 4; i = i + 1)
    for(Integer j = 0; j < 4; j = j + 1)
      ls[i][j] = i + j;

  Reg#(UInt#(3)) j <- mkReg(0);

  let l = ls[j];
  l[2] = 0;

  rule test;
    $display("{%0d,%0d,%0d,%0d}", l[0], l[1], l[2], l[3]);
    if (j == 3) $finish(0);
    j <= j + 1;
  endrule

endmodule

