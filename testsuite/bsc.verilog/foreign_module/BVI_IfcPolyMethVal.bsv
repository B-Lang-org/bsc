interface Ifc;
   method a m();
endinterface

import "BVI"
module mkMod(Ifc);
  default_clock clk();
  default_reset rst();
endmodule

