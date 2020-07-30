interface Ifc#(type a);
   method a#(8) m();
endinterface

import "BVI"
module mkMod(Ifc#(Bit));
  default_clock clk();
  default_reset rst();
  method RES m();
  schedule m CF m;
endmodule

