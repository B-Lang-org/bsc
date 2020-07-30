package MkRequestResponseBuffer1;

import ClientServer :: *;
import GetPut :: *;
import Connectable :: *;


module mkDesign_MkRequestResponseBuffer1(ClientServer #(Bit#(8),Bit#(8)) );
   ClientServer #(Bit #(8),Bit#(8)) dut();
   mkRequestResponseBuffer1 the_dut(dut);
   return(dut);
endmodule: mkDesign_MkRequestResponseBuffer1


module mkTestbench_MkRequestResponseBuffer1 ();

   ClientServer #(Bit #(8),Bit#(8)) tx_datafifo();
   mkRequestResponseBuffer1 the_tx_datafifo(tx_datafifo);
   Reg#(Bit#(8)) in_data1 <- mkReg(0);
   Reg#(Bit#(8)) in_data2 <- mkReg(0);
   Reg#(Bit#(8)) out_data1 <- mkReg(0);
   Reg#(Bit#(8)) out_data2 <- mkReg(0);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write1 (True);
	 (Server#(Bit#(8),Bit#(8))'(tpl_2(tx_datafifo))).request.put(in_data1);
     in_data1 <= in_data1 + 1;
     $display("Cycle Number: %d, Writing Data On Server Side: %d", counter, in_data1);
   endrule
   
   rule data_write2 (True);
	 (Client#(Bit#(8),Bit#(8))'(tpl_1(tx_datafifo))).response.put(in_data2);
     in_data2 <= in_data2 + 5;
     $display("Cycle Number: %d, Writing Data On Client Side: %d", counter, in_data2);
   endrule

   rule read_value1 (True); 
	 Bit#(8) first <- (Client#(Bit#(8),Bit#(8))'(tpl_1(tx_datafifo))).request.get;
     out_data1 <= out_data1 + 1;
	 $display("Cycle Number = %d, Value read from Client Side= %d",counter, first);
     if (out_data1 != first)
         fail <= True;
  endrule

   rule read_value2 (True); 
	 Bit#(8) second <- (Server#(Bit#(8),Bit#(8))'(tpl_2(tx_datafifo))).response.get;
     out_data2 <= out_data2 + 5;
	 $display("Cycle Number = %d, Value read from Server Side= %d",counter, second);
     if ((out_data2 != second))
         fail <= True;
  endrule
  rule endofsim (counter == 10);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule : mkTestbench_MkRequestResponseBuffer1

endpackage : MkRequestResponseBuffer1
