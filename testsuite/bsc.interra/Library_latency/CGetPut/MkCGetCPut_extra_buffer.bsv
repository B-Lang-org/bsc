package MkCGetCPut_Mk_extrabuffer;

import CGetPut :: *;
import GetPut :: *;
import Connectable :: *;


module mkDesign_MkCGetCPut(Tuple2#(CGet#(2,Bit #(8)),CPut#(2,Bit#(8)))) ;
  Tuple2#(CGet#(2,Bit #(8)),CPut#(2,Bit#(8))) dut();
  mkCGetCPut the_dut (dut);
  return dut;
endmodule: mkDesign_MkCGetCPut


module mkTestbench_Mk_extrabuffer ();

   Tuple2#(CGet#(4,Bit #(8)),CPut#(4,Bit#(8))) testfifo();
   mkCGetCPut the_testfifo (testfifo);

   CGetPut #(4,Bit #(8)) tx_datafifo();
   mkCGetPut the_tx_datafifo (tx_datafifo);
   
   GetCPut #(4,Bit #(8)) rx_datafifo();
   mkGetCPut the_rx_datafifo (rx_datafifo);

   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

   Empty tx_to_testfifo <- mkConnection (tpl_1(tx_datafifo) ,tpl_2(testfifo) );
   Empty testfifo_to_rx <- mkConnection (tpl_1(testfifo) ,tpl_2(rx_datafifo) );

rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (counter == 0  || counter == 1 );
     tpl_2(tx_datafifo).put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule
   

   rule read_value (counter > 1 );
     Bit #(8) first <- tpl_1(rx_datafifo).get;
     out_data <= out_data + 1;
	  $display ("Counter value at read: %d", counter );
	 $display("Cycle Number = %d, Value read = %d",counter, first);
     if (out_data != first)
         fail <= True;
  endrule

  rule endofsim (counter == 100);
	if (fail)
	  $display("Simulation Fails");
	else
	  begin
	  $display ("Counter value: %d", counter );
	  $display("Simulation Passes");
	end
	$finish(2'b00);
  endrule

endmodule : mkTestbench_Mk_extrabuffer

endpackage : MkCGetCPut_Mk_extrabuffer
