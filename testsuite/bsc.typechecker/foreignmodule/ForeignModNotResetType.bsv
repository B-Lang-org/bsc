interface IFC;
   interface Bool rst_out;
endinterface

import "BVI" Mod =
   module mkMod(IFC);
      default_clock no_clock;
      default_reset rst(IN_RST_N);
      output_reset rst_out(OUT_RST_N);
   endmodule

