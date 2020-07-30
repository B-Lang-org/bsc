interface IFC;
   interface Bool out_clk;
endinterface

import "BVI" Mod =
   module mkMod(IFC);
      default_clock in_clk(IN_CLK);
      no_reset;
      output_clock out_clk(OUT_CLK);
   endmodule

