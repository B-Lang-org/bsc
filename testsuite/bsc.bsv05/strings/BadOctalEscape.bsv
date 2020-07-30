(* synthesize *)
module sysBadChar();
  rule test;
    $display("\378");
    $finish(0);
  endrule
endmodule
