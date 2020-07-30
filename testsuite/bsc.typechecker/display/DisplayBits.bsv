(* synthesize *)
module sysDisplayBits ();

  Reg#(Bool) done <- mkReg(False);

  rule do_display (!done);
     Bit#(1) t = 1;
     Bit#(1) f = 0;
     $display(unpack(t), " ", unpack(f));
     done <= True;
  endrule

  rule do_finish (done);
     $finish(0);
  endrule

endmodule
