//Negative Testcase 

import Clocks::*;

interface Design_IFC;
 method Action start(Bit#(6) in_data1, Bit#(6) in_data2); 
 method Bit#(7) out_data();
 interface Clock clk_fast;
endinterface : Design_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkDesign (Design_IFC ifc);
 Reset currRst <- exposeCurrentReset;

 ClockDividerIfc    div();
 mkClockDivider#(4) t_div(div);

 //mkSyncRegToFast is uninitialized it should be mkSyncRegToFast#(?)

 Reg#(Bit#(7))         out_data_reg() ;
 mkSyncRegToFast       i_out_data_reg(div, currRst, out_data_reg);

 method Action start(data1, data2);
	out_data_reg <= zeroExtend(data1) + zeroExtend(data2);
 endmethod : start

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data

 interface Clock clk_fast = div.slowClock;
endmodule
