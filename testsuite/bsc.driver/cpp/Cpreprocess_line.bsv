#include "more.bsv"
module cpreprocess();
   Reg#(int) i <- mkReg(190);
   int x = False;
   rule rule1;
      $display(i);
      $finish(0);
   endrule
endmodule
