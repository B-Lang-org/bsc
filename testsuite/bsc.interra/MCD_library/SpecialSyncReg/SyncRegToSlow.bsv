//Testcase 

import Clocks::*;

interface SyncRegSlow_IFC;
 method Action start(Bit#(6) in_data1, Bit#(6) in_data2); 
 method Bit#(7) out_data();
 interface Clock clk_slow;
 interface Reset rst_slow;
endinterface : SyncRegSlow_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkSyncRegSlow (Clock clk_fast, SyncRegSlow_IFC ifc);
 Clock currClk <- exposeCurrentClock;
 Reset currRst <- exposeCurrentReset;

 ClockDividerIfc    div();
 mkClockDivider#(4) t_div(div, clocked_by clk_fast, reset_by noReset);

 Reset                 rst_n();
 mkSyncResetFromCR#(3) t_rst_n(div.slowClock, rst_n);

 Reg#(Bit#(7))         out_data_reg() ;
 mkSyncRegToSlow#(0)   i_out_data_reg(div, rst_n, out_data_reg);

 method Action start(data1, data2);
	out_data_reg <= zeroExtend(data1) + zeroExtend(data2);
 endmethod : start

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data

 interface Clock clk_slow = div.slowClock;

 interface Reset rst_slow = rst_n;
endmodule
