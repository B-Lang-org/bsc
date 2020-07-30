//Testcase 

import Clocks::*;

interface Design_IFC;
 method Action inp_clk1(Bit#(6) in_data);
 method Bool ack();
 method Bit#(6) out_data();
endinterface : Design_IFC

(* 
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkDesign#(Clock clk_2, Reset rst_2) (Design_IFC);
 RWire#(Bit#(6))  in_data();
 mkRWire          t_in_data(in_data);

 SyncPulseIfc              bitToClk1() ;
 mkSyncHandshakeToCC       i_bitToClk1( clk_2,  rst_2, bitToClk1);

 method Action inp_clk1(data);
	in_data.wset(data);
	bitToClk1.send;
 endmethod : inp_clk1

 method ack();
   ack = bitToClk1.pulse;
 endmethod : ack

 method out_data() if (bitToClk1.pulse);
   out_data = validValue(in_data.wget);
 endmethod : out_data
endmodule
