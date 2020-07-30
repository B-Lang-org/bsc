export sysNegativeDisplay;

module sysNegativeDisplay(Empty);
  rule main
    (True()); $display("%0d",-5); $finish(0);
  endrule: main
endmodule: sysNegativeDisplay
