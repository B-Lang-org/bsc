import List::*;

(* synthesize *)
module sysSelectListUndefinedIndex();
  
  List#(Integer) l = cons(1, cons(2, cons(3, cons(4, nil))));

  Reg#(Bool) r <- mkReg(False);

  rule test;
    $display("%0d", l[?]);
    $finish(0);
  endrule

endmodule
