// For some reason, this example tickled a bug in BSC
// that the other example did not.

(* synthesize *)
module sysRealDisplay2 ();

  Reg#(Bool) done <- mkReg(False);

  Real r = 0.1;
  rule do_disp (!done);
     $display("foo: %f", r);
     done <= True;
  endrule

  rule do_done (done);
     $finish(0);
  endrule
endmodule

