
module sysBug262Opt(Empty);

  Reg#(Maybe#(Bit#(19))) r <- mkReg(Invalid);

  Reg#(Bool) done <- mkReg(False);

  rule start (!done);
    r <= tagged Valid 5;
    done <= True;
  endrule

  rule finish(done);
    r <= tagged Invalid;
    $finish(0);
  endrule
endmodule

