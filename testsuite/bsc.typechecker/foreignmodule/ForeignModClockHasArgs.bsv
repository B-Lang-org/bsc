interface IFC;
   method Clock out_clk(Bool b);
endinterface

import "BVI" Mod =
   module mkMod(IFC);
      default_clock in_clk(IN_CLK);
      no_reset;
      output_clock out_clk(OUT_CLK);
   endmodule

