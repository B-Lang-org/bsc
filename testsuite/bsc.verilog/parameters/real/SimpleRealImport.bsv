import "BVI" DisplayReal =
module vDisplayReal#(real r)(Empty ifc);
   
   default_clock clk(CLK, (* unused *) CLK_GATE);
   default_reset no_reset;
   
   parameter val = r;
   
endmodule

(* synthesize *)
module sysSimpleRealImport();

   // $finish is in the dut
   Empty dut <- vDisplayReal(17.23);
   
endmodule
