package MkBClientServer;

import ClientServer :: *;
import BGetPut :: *;
import GetPut :: *;
import Connectable :: *;

module mkDesign_MkBClientServer(BClientServer #(Bit #(8),Bit #(8))) ;
   BClientServer #(Bit #(8),Bit #(8)) dut();
   mkBClientServer the_dut (dut);
   return dut;
endmodule: mkDesign_MkBClientServer

module mkTestbench_MkBClientServer ();

   BClientServer #(Bit #(8),Bit #(8)) tx_datafifo();
   mkBClientServer the_tx_datafifo (tx_datafifo);
   ClientBServer #(Bit #(8),Bit #(8)) rx_datafifo();
   mkClientBServer the_rx_datafifo (rx_datafifo);
   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

   Empty joinfifos <- mkConnection (tpl_1(tx_datafifo) ,tpl_2(rx_datafifo) );

rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (counter < 20 || counter > 60);
	 (Server#(Bit#(8),Bit#(8))'(tpl_2(tx_datafifo))).request.put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule
   

   rule read_value (counter < 9 || counter > 15 );
     Bit#(8) first <- (Client#(Bit#(8),Bit#(8))'(tpl_1(rx_datafifo))).request.get;
     out_data <= out_data + 1;
	 $display("Cycle Number = %d, Value read = %d",counter, first);
     if (out_data != first)
         fail <= True;
  endrule

  rule endofsim (counter == 60);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule : mkTestbench_MkBClientServer

endpackage : MkBClientServer
