//Testcase for clock domain crossing using Bit synchronizer : MCD
//This module's output samples in_data[7:0] or in_data[15:8], depending on 
//select bit,which is coming from "2" domain, whereas data is in "1" domain.

import Clocks::*;

interface Design_IFC;
 method Action inp_clk1(Bit#(16) in_data);
 method Action inp_clk2(Bit#(1) sel); 
 method Bit#(8) out_data();
endinterface : Design_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkDesign (Clock clk_2, Reset rst_2, Design_IFC ifc);
 Reg#(Bit#(8))     out_data_reg();
 mkReg#(0)         t_out_data_reg(out_data_reg);

 Clock currClk <- exposeCurrentClock; 
 Reset currRst <- exposeCurrentReset;

 SyncBitIfc#(Bit#(1))       bitToClk1() ;
 mkSyncBit        i_bitToClk1( clk_2,  rst_2, currClk, bitToClk1);

 SyncPulseIfc       pulseToClk2() ;
 mkSyncPulse        i_pulseToClk2( clk_2,  currRst, clk_2, pulseToClk2);

 method Action inp_clk1(in_data1);
	out_data_reg <= (bitToClk1.read == 0) ? in_data1[7:0] : in_data1[15:8];
	pulseToClk2.send;
 endmethod : inp_clk1

 method Action inp_clk2(sel1);
	if(pulseToClk2.pulse)
	  bitToClk1.send(sel1);
 endmethod : inp_clk2

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data
endmodule
