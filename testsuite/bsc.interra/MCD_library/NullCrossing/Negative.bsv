//Negative Testcase 

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

 Reg#(Bit#(1))       flopA_clk2();
 mkReg#(0)           t_flopA_clk2(flopA_clk2, clocked_by clk_2, reset_by rst_2);

 Reg#(Bit#(1))       flopB();
 mkReg#(0)           t_flopB(flopB);

 Reg#(Bit#(1))       flopC();
 mkReg#(0)           t_flopC(flopC);

 //Clocking is inappropriate and gives clock domain crossing error

 ReadOnly#(Bit#(1))  flopA_clk1();
 mkNullCrossing      t_flopA_clk1(clk_2, flopA_clk2, flopA_clk1);

 SyncPulseIfc       pulseToClk2() ;
 mkSyncPulse        i_pulseToClk2( currClk,  currRst, clk_2, pulseToClk2);

 method Action inp_clk1(in_data1);
	flopB <= flopA_clk1._read;
	flopC <= flopB;
	out_data_reg <= (flopC == 0) ? in_data1[7:0] : in_data1[15:8];
	pulseToClk2.send;
 endmethod : inp_clk1

 method Action inp_clk2(sel1);
	if(pulseToClk2.pulse)
	  flopA_clk2 <= sel1;
 endmethod : inp_clk2

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data
endmodule
