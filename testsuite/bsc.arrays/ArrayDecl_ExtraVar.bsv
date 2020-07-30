
(* synthesize *)
module sysArrayDecl_ExtraVar ();

  Bool arrA[3] = {True, False, True}, arrB[2] = { True, True };

  // need to use the value, for the size check to be evaluated
  rule r;
    $display(arrA[0]);
    $display(arrB[0]);
  endrule

endmodule

