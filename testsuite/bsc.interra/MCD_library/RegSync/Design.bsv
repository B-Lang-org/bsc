//Testcase for clock domain crossing using Register synchronizer : MCD
//This module takes data1 and data2 as input. After adding data1 and data2
//output data is send to different domain.

import Clocks::*;

interface Design_IFC;
 method Action start(Bit#(6) in_data1, Bit#(6) in_data2); 
 method Bit#(7) out_data();
endinterface : Design_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkDesign#(Clock clk_2, Reset rst_2) (Design_IFC);
 Reg#(Bit#(7))         out_data_reg() ;
 mkSyncRegFromCC#(0)   i_out_data_reg(clk_2, out_data_reg);

 method Action start(data1, data2);
	out_data_reg <= zeroExtend(data1) + zeroExtend(data2);
 endmethod : start

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data
endmodule
