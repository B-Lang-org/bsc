interface Ifc;
   method a#(b) m();
endinterface

import "BVI"
module mkMod(Ifc);
  default_clock clk();
  default_reset rst();
endmodule

