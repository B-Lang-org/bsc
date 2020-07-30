package MkSizedRequestResponseBuffer;

import ClientServer :: *;
import GetPut :: *;
import Connectable :: *;


module mkDesign_MkSizedRequestResponseBuffer(ClientServer #(Bit#(8),Bit#(8)) );
   ClientServer #(Bit #(8),Bit#(8)) dut();
   mkSizedRequestResponseBuffer#(16) the_dut(dut);
   return(dut);
endmodule: mkDesign_MkSizedRequestResponseBuffer


module mkTestbench_MkSizedRequestResponseBuffer ();

   ClientServer #(Bit #(8),Bit#(8)) tx_datafifo();
   mkSizedRequestResponseBuffer#(16) the_tx_datafifo(tx_datafifo);
   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (counter < 18);
	 (Server#(Bit#(8),Bit#(8))'(tpl_2(tx_datafifo))).request.put(in_data);
	 (Client#(Bit#(8),Bit#(8))'(tpl_1(tx_datafifo))).response.put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule
   

   rule read_value (counter >= 18); 
	 Bit#(8) first <- (Client#(Bit#(8),Bit#(8))'(tpl_1(tx_datafifo))).request.get;
	 Bit#(8) second <- (Server#(Bit#(8),Bit#(8))'(tpl_2(tx_datafifo))).response.get;
     out_data <= out_data + 1;
	 $display("Cycle Number = %d, Value read = %d",counter, first);
     if ((out_data != first) || (out_data != second))
         fail <= True;
  endrule

  rule endofsim (counter == 50);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule : mkTestbench_MkSizedRequestResponseBuffer

endpackage : MkSizedRequestResponseBuffer
