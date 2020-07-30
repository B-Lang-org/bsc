package MkConnection;

import GetPut :: *;
import Connectable :: *;

module mkTestbench_MkConnection ();

   GetPut #(Bit #(8)) dut1();
   mkGPFIFO the_dut1 (dut1);
   
   GetPut #(Bit #(8)) dut2();
   mkGPFIFO the_dut2 (dut2);

   Get #(Bit #(8)) dut1Get = tpl_1 (dut1);
   Put #(Bit #(8)) dut2Put = tpl_2 (dut2);
    
   Empty join12();
   mkConnection #(dut1Get, dut2Put) the_join12(join12);
   
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bit#(8)) in_data <- mkReg(0);
   Reg#(Bit#(8)) out_data <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);


   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (counter < 20 || counter > 30);
     tpl_2(dut1).put(in_data);
     in_data <= in_data + 1;
     $display("Cycle Number: %d, Writing Data: %d", counter, in_data);
   endrule
   

   rule read_value (counter < 9 || counter > 15 );
     Bit #(8) first <- tpl_1(dut2).get;
     out_data <= out_data + 1;
	 $display("Cycle Number = %d, Value read = %d",counter, first);
     if (out_data != first)
         fail <= True;
  endrule


  rule endofsim (counter == 40);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule



endmodule : mkTestbench_MkConnection
endpackage : MkConnection
