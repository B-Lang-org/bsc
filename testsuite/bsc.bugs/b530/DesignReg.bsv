package DesignReg;

module sysDesignReg ();
  Reg#(int) r <- mkReg(-1);
  Reg#(int) out <- mkRegU();
  Reg#(Bool) print <- mkReg(False);
  Reg#(Bool) quit <- mkReg(False);
  rule r1;
    // a negative shift should cause a runtime error in simulation
    out <= 1<< r;
    print <= True;
  endrule
  rule r2 (print);
    $display(out);
    quit <= True;
  endrule
  rule r3 (quit);
    $finish(0);
  endrule
  

endmodule
endpackage
