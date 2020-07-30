package MkBGetPut;

import BGetPut :: *;
import GetPut :: *;
import Connectable :: *;

module mkDesign_MkBGetPut(BGetPut #(Bit #(8))) ;
   BGetPut #(Bit #(8)) dut();
   mkBGetPut the_dut (dut);
   return dut;
endmodule: mkDesign_MkBGetPut


module mkTestbench_MkBGetPut ();

   BGetPut #(Bit #(8)) tx_datafifo();
   mkBGetPut the_tx_datafifo (tx_datafifo);
   GetBPut #(Bit #(8)) rx_datafifo();
   mkGetBPut the_rx_datafifo (rx_datafifo);

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

   rule data_write (counter_w < 40   );
     tpl_2(tx_datafifo).put(in_data);
     in_data <= in_data + 1;
     $display("WRITING : Cycle Number: %d, Writing Data: %d", counter_w, in_data);
   endrule
   

 rule read_value ( counter_r <  40  );
         Bit #(8) first <- tpl_1(rx_datafifo).get;
     out_data <= out_data + 1;
     $display("READING Cycle Number = %d, Value read = %d",counter_r, first);
     if (out_data != first)
         fail <= True;
  endrule

  rule endofsim (counter_w > 38 );
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule : mkTestbench_MkBGetPut

endpackage : MkBGetPut
