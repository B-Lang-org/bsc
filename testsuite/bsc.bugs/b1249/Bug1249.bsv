interface Bug;
  method Bool getGateCond();
  interface Clock new_clk;
endinterface

(* synthesize *)
module sysBug ( Bug ifc );
   
   Bug m <- vMkBug();

   method getGateCond = m.getGateCond;
   interface new_clk = m.new_clk;
endmodule

import "BVI" MakeBug = 
module vMkBug ( Bug );

   default_clock clk(CLK, (* unused *) CLK_GATE) ;
   no_reset;

   method CLK_GATE_OUT getGateCond() ;

   // get methods are CF with themselves
   schedule getGateCond CF getGateCond;

   output_clock new_clk(CLK_OUT, CLK_GATE_OUT);
endmodule
