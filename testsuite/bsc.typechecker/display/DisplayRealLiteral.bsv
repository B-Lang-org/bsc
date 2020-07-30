(* synthesize *)
module sysDisplayRealLiteral ();

  Reg#(Bool) done <- mkReg(False);

  rule do_display (!done);
     $display(0.5, " ", 1.5, " ", 2.5, " ", 3.5);
     done <= True;
  endrule

  rule do_finish (done);
     $finish(0);
  endrule

endmodule
