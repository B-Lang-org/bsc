// Latency is 4 clock cycles 
// GetPut interface is taking one clock cycle
// to write and one clock cycle to read
// internally . This is in sync with the 
// document .
package MkCGetPut;

import CGetPut :: *;
import GetPut :: *;
import Connectable :: *;

module mkDesign_MkCGetPut(CGetPut #(2,Bit #(8))) ;
   CGetPut #(2,Bit #(8)) dut();
   mkCGetPut the_dut (dut);
   return dut;
endmodule: mkDesign_MkCGetPut


module mkTestbench_MkCGetPut ();

   CGetPut #(5,Bit #(8)) tx_datafifo();
   mkCGetPut the_tx_datafifo (tx_datafifo);
   GetCPut #(5,Bit #(8)) rx_datafifo();
   mkGetCPut the_rx_datafifo (rx_datafifo);
   Reg#(Bit#(8)) in_data <- mkReg(2);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter_w <- mkReg(0);
   Reg#(Bit#(8)) counter_r <- mkReg(0);

   Reg#(Bool) fail <- mkReg(False);



   Empty joinfifos <- mkConnection (tpl_1(tx_datafifo) ,tpl_2(rx_datafifo) );
   

rule always_fire_write (True);
   	 counter_w <= counter_w + 1;
         counter_r <= counter_r + 1;
   endrule

   rule data_write (counter_w < 12   );
     tpl_2(tx_datafifo).put(in_data);
     in_data <= in_data + 1;
     $display("WRITING : Cycle Number: %d, Writing Data: %d", counter_w, in_data);
   endrule
   

 rule read_value ( counter_r <  12  );
         Bit #(8) first <- tpl_1(rx_datafifo).get;
     out_data <= out_data + 1;
     $display("READING Cycle Number = %d, Value read = %d",counter_r, first);
     if (out_data != first)
         fail <= True;
  endrule

  rule endofsim (counter_w > 20 );
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule : mkTestbench_MkCGetPut

endpackage : MkCGetPut
