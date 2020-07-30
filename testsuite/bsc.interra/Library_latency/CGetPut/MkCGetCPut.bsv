package MkCGetCPut;

import CGetPut :: *;
import GetPut :: *;
import Connectable :: *;

module mkDesign_MkCGetCPut(Tuple2#(CGet#(2,Bit #(8)),CPut#(2,Bit#(8)))) ;
   Tuple2#(CGet#(2,Bit #(8)),CPut#(2,Bit#(8))) dut();
   mkCGetCPut the_dut (dut);
   return dut;
endmodule: mkDesign_MkCGetCPut


module mkTestbench_MkCGetCPut ();

   Tuple2#(CGet#(6,Bit #(8)),CPut#(6,Bit#(8))) testfifo();
   mkCGetCPut the_testfifo (testfifo);

   CGetPut #(6,Bit #(8)) tx_datafifo();
   mkCGetPut the_tx_datafifo (tx_datafifo);
   
   GetCPut #(6,Bit #(8)) rx_datafifo();
   mkGetCPut the_rx_datafifo (rx_datafifo);

   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bit#(8)) counter_w <- mkReg(0);
   Reg#(Bit#(8)) counter_r <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);

   Empty tx_to_testfifo <- mkConnection (tpl_1(tx_datafifo) ,tpl_2(testfifo) );
   Empty testfifo_to_rx <- mkConnection (tpl_1(testfifo) ,tpl_2(rx_datafifo) );


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

  rule endofsim (counter_w > 12 );
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule
endmodule : mkTestbench_MkCGetCPut
endpackage : MkCGetCPut
