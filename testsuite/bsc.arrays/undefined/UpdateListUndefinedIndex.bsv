import List::*;

(* synthesize *)
module sysUpdateListUndefinedIndex();

  List#(int) l = cons(1, cons(2, cons(3, cons(4, nil))));

  l[?] = 0;

  rule test;
    $display(l[0]);
  endrule
 
endmodule