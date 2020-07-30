(* synthesize *)
module sysSelectUndefinedListStatic();
  
  List#(Maybe#(Bool)) l = ?;

  rule test;
    $display("%0d", l[1]);
    $finish(0);
  endrule

endmodule
