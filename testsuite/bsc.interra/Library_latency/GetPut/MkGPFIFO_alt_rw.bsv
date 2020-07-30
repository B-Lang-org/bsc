package MkGPFIFO;

import GetPut :: *;

module mkDesign_MkGPFIFO(GetPut #(Bit #(8))) ;
   GetPut #(Bit #(8)) dut();
   mkGPFIFO the_dut (dut);
   return dut;
endmodule: mkDesign_MkGPFIFO

module mkTestbench_MkGPFIFO_alt_rw ();

   GetPut #(Bit #(8)) datafifo();
   mkGPFIFO the_datafifo (datafifo);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);


  rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (counter[0:0] == 0); 
     tpl_2(datafifo).put(counter+8'd15);
      $display("Value Written = %d time = %d counter = %d",(counter+8'd15),$time,counter);
   endrule
   

   

   rule read_value ( counter[0:0] != 0);
     Bit #(8) first <- tpl_1(datafifo).get;
	 $display("Value read = %d time = %d counter = %d",first,$time,counter);
	 if (first != (counter+15 -1))
	   fail <= True;
  endrule

  rule endofsim (counter == 22);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule



endmodule : mkTestbench_MkGPFIFO_alt_rw
endpackage : MkGPFIFO
