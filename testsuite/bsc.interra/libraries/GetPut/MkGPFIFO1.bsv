package MkGPFIFO1;

import GetPut :: *;


module mkDesign_MkGPFIFO1(GetPut #(Bit #(8))) ;
   GetPut #(Bit #(8)) dut();
   mkGPFIFO1 the_dut (dut);
   return dut;
endmodule: mkDesign_MkGPFIFO1

module mkTestbench_MkGPFIFO1 ();
        
  GetPut #(Bit#(8)) datafifo();
  mkGPFIFO1 the_datafifo (datafifo);
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 1);
     tpl_2(datafifo).put(counter+8'd15);
  endrule

  rule read_value ((counter >=2) && (counter < 3));
     Bit #(8) first <- tpl_1 (datafifo).get;
	 $display("Value read = %h",first);
	 if (first != (counter+15-2))
	   fail <= True;
  endrule


  rule read1_value ((counter >=5) && (counter < 6));
     tpl_2(datafifo).put(counter+8'd25);
  endrule

 rule read_value2 ((counter >=6) && (counter < 7));
     Bit #(8) first <- tpl_1 (datafifo).get;
	 $display("Value read = %h",first);
	 if (first != (counter+25-1))
	   fail <= True;
  endrule

  rule write_excess ((counter >=7) && (counter < 20));
     tpl_2(datafifo).put(counter+8'd6);
	 $display("Value Written = %h",(counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 21));
     Bit #(8) first <- tpl_1 (datafifo).get;
	 $display("Value read = %h",first);
	 if (first != (counter+6-13))
	   fail <= True;
  endrule

  rule endofsim (counter == 21);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkGPFIFO1 
endpackage: MkGPFIFO1
