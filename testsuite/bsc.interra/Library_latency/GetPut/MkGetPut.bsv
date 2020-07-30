package MkGetPut;

import GetPut :: *;

module mkDesign_MkGetPut(GetPut #(Bit #(8))) ;
   GetPut #(Bit #(8)) dut();
   mkGetPut the_dut (dut);
   return dut;
endmodule: mkDesign_MkGetPut

module mkTestbench_MkGetPut ();

   GetPut #(Bit #(8)) datafifo();
   mkGetPut the_datafifo (datafifo);
   Reg#(Bit#(8)) counter <- mkReg(0);
   Reg#(Bool) fail <- mkReg(False);


   rule always_fire (True);
   	 counter <= counter + 1;
   endrule

   rule data_write (counter < 2);
     tpl_2(datafifo).put(counter+8'd15);
   endrule
   

   rule read_value ((counter >=2) && (counter < 4));
     Bit #(8) first <- tpl_1(datafifo).get;
	 $display("Value read = %h",first);
	 if (first != (counter+15-2))
	   fail <= True;
  endrule

  rule read1_value ((counter >=7) && (counter < 9));
     tpl_2(datafifo).put(counter+25);
  endrule

  rule read_value2 ((counter >=9) && (counter < 11));
     Bit #(8) first <- tpl_1(datafifo).get;
	 $display("Value read = %h",first);
	 if (first != (counter+25-2))
	   fail <= True;
  endrule

  rule write_excess ((counter >=11) && (counter < 20));
     tpl_2(datafifo).put(counter+6);
	 $display("Value Written = %h",(counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 22));
     Bit #(8) first <- tpl_1(datafifo).get;
     $display("Value read = %h",first);
	 if (first != (counter+6-9))
	   fail <= True;
  endrule

  rule endofsim (counter == 22);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule



endmodule : mkTestbench_MkGetPut
endpackage : MkGetPut
