import List::*;
// Test updating a list based on a dynamic index
// that is the result of a dynamic selection
(* synthesize *)
module sysTwoLevelUpdateList();

  List#(int) l = cons(1, cons(2, cons(3, cons(4, nil))));
  int indices[4] = {0, 3, 2, 1};

  Reg#(UInt#(3)) j <- mkReg(0);

  l[indices[j]] = 0;

  rule test;
    $display("{%0d,%0d,%0d,%0d}", l[0], l[1], l[2], l[3]);
    if (j == 3) $finish(0);
    j <= j + 1;
  endrule

endmodule

