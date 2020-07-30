interface Ifc#(type a);
   method a m();
endinterface

import "BVI"
module mkMod(Ifc#(b));
  default_clock clk();
  default_reset rst();
  method RES m();
  schedule m CF m;
endmodule

