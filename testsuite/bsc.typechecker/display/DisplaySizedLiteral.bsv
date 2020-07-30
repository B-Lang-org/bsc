(* synthesize *)
module sysDisplaySizedLiteral ();

  Reg#(Bool) done <- mkReg(False);

  rule do_display (!done);
     $display(4'b1111, " ", 5'b10000, " ", 1'b1, " ", 1'b0);
     done <= True;
  endrule

  rule do_finish (done);
     $finish(0);
  endrule

endmodule
