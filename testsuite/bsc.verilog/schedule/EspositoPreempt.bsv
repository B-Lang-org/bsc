package EspositoPreempt;

module sysEspositoPreempt(Empty);

  Reg#(Bit#(32)) x();
  mkReg#(0) the_x(x);

  Reg#(Bool) done();
  mkReg#(False) the_done(done);

  rule set_done
   (True); done <= True;
  endrule: set_done

  rule exit
   (done); $finish(0);
  endrule: exit

  rule b
   (True); x <= x + 2; $display("b");
  endrule: b

  rule a
   (True); $display("a"); x <= x + 1;
  endrule: a

endmodule: sysEspositoPreempt

endpackage
