//Testcase 

import Clocks::*;

interface SyncRegFast_IFC;
 method Action start(Bit#(6) in_data1, Bit#(6) in_data2); 
 method Bit#(7) out_data();
 interface Clock clk_slow;
 interface Reset rst_slw;
endinterface : SyncRegFast_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkSyncRegFast (SyncRegFast_IFC ifc);

 ClockDividerIfc    div();
 mkClockDivider#(4) t_div( div);

 Reset                 rst_slow();
 mkAsyncResetFromCR#(3) t_rst_slow(div.slowClock, rst_slow);

 Reg#(Bit#(7))         out_data_reg() ;
 mkSyncRegToFast#(0)   i_out_data_reg(div, rst_slow, out_data_reg);

 method Action start(data1, data2);
	out_data_reg <= zeroExtend(data1) + zeroExtend(data2);
 endmethod : start

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data

 interface Clock clk_slow = div.slowClock;

 interface Reset rst_slw = rst_slow;
endmodule
