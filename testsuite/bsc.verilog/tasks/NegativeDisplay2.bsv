export sysNegativeDisplay2;

module sysNegativeDisplay2(Empty);
  rule main
    (True()); $display("%0d",Integer'(-5)); $finish(0);
  endrule: main
endmodule: sysNegativeDisplay2
