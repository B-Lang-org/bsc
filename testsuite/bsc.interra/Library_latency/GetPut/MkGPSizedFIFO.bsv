package MkGPSizedFIFO;

import GetPut :: *;

module mkDesign_MkGPSizedFIFO(GetPut #(Bit #(8))) ;
   GetPut #(Bit #(8)) dut();
   mkGPSizedFIFO #(16) the_dut (dut);
   return dut;
endmodule: mkDesign_MkGPSizedFIFO


module mkTestbench_MkGPSizedFIFO ();
        
  GetPut#(Bit#(8)) datafifo();
  mkGPSizedFIFO #(16) the_datafifo (datafifo) ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 16);
     tpl_2(datafifo).put(counter+15);
  endrule

  rule read_value ((counter >=16) && (counter < 32));
	 Bit #(8) first <- tpl_1(datafifo).get;
     $display("Counter = %d Value read = %h",counter,first);
	 if (first != (counter+15-16))
	   fail <= True;
  endrule


  rule read1_value ((counter >=49) && (counter < 65));
     tpl_2(datafifo).put(counter - 49 );
  endrule

  rule read_value2 ((counter >= 8'd65) && (counter < 8'd81));
	 Bit #(8) first <- tpl_1(datafifo).get;
	 $display("Counter = %d Value read = %h",counter,first);
	 if (first != (counter-65))
	   fail <= True;
  endrule

  rule write_excess ((counter >=81) && (counter < 111));
     tpl_2(datafifo).put(counter);
	 $display("Value Written = %h",counter);
  endrule

  rule read_value_excess ((counter >=111) && (counter < 128));
	 Bit #(8) first <- tpl_1(datafifo).get;
	 $display("Counter = %d Value read = %h",counter,first);
	 if (first != (counter-30))
	   fail <= True;
  endrule

  rule data_write2 ((counter >=128) && (counter < 133));
     tpl_2(datafifo).put(counter-128);
  endrule

  rule data_read2 ((counter >=133) && (counter < 138));
	 Bit #(8) first <- tpl_1(datafifo).get;
	 $display("Counter = %d Value read = %h",counter,first);
	 if (first != (counter-133))
	   fail <= True;
     tpl_2(datafifo).put(counter);
  endrule

  rule endofsim (counter == 138);
	if (fail)
	  $display("counter = %d Simulation Fails",counter);
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkGPSizedFIFO 
endpackage: MkGPSizedFIFO
