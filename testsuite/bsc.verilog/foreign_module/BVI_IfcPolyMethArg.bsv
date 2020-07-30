interface Ifc;
   method Bool m(a x);
endinterface

import "BVI"
module mkMod(Ifc);
  default_clock clk();
  default_reset rst();
endmodule

