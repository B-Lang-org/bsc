#include "number.h"
module sysCpreprocess();
   Reg#(int) i <- mkReg(190);
   rule rule1;
      $display(i);
      $display(NUMBER);
      $display(MESSAGE);
      $finish(0);
   endrule
endmodule
