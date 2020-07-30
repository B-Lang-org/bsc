package DynamicAssert;

import FIFO::*;
import Assert:: *;


module mkTestbench_DynamicAssert ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFO#(Bit#(8)) datafifo <- mkFIFO() ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(8)) count1 <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);
 
  
  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule test_assertion (True);
     dynamicAssert (!fail, "Failure: Fail becomes True");
  endrule
  
  rule data_write_a (counter < 2);
     datafifo.enq(counter+15);
  endrule

  rule read_value_a ((counter >=2) && (counter < 4));
	 $display("Value read = %h",datafifo.first);
	 if (datafifo.first != (counter+15-2))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write_b ((counter >=4) && (counter < 6));
     datafifo.enq(counter+15);
  endrule

  rule clear_fifo (counter == 6);
	 datafifo.clear;
  endrule

  rule read_value_b ((counter >=7) && (counter < 9));
     datafifo.enq(counter+25);
  endrule

  rule read_value_c ((counter >=9) && (counter < 11));
	 $display("Value read = %h",datafifo.first);
	 if (datafifo.first != (counter+25-2))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule write_excess ((counter >=11) && (counter < 20));
     datafifo.enq(counter+6);
	 $display("Value Written = %h",(counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 22));
	 $display("Value read = %h",datafifo.first);
	 if (datafifo.first != (counter+6-8)) //Assertion Fails here. Use counter +6-9
	   fail <= True;
	 datafifo.deq;
  endrule

  rule endofsim (counter == 22);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_DynamicAssert 
endpackage: DynamicAssert
