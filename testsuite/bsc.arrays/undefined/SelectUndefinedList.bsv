(* synthesize *)
module sysSelectUndefinedList();
  
  List#(int) l = ?;

  Reg#(Bool) r <- mkReg(False);

  rule test;
    $display(l[r ? 0 : 1]);
    r <= !r;
    if (r) $finish(0);
  endrule

endmodule
