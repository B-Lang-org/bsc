(* synthesize *)
module sysDisplayLiteral ();

  Reg#(Bool) done <- mkReg(False);

  rule do_display (!done);
     $display(0, " ", 1, " ", 2, " ", 3);
     done <= True;
  endrule

  rule do_finish (done);
     $finish(0);
  endrule

endmodule
