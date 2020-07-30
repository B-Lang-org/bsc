package FifoToPut;

import GetPut :: *;
import FIFO :: *;

//mkDesign_FifoToPut just to see if a proper verilog is created.
module mkDesign_FifoToPut(Put #(Bit #(8) )); 
     FIFO#(Bit #(8)) f(); 
     mkFIFO the_f(f); 
     return (fifoToPut(f)); 
endmodule: mkDesign_FifoToPut

module mkTestbench_FifoToPut ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFO#(Bit#(8)) dut <- mkFIFO() ;
  Put#(Bit#(8)) dutput = fifoToPut (dut) ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(8)) count1 <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 2);
     dutput.put(counter+15);
  endrule

  rule read_value ((counter >=2) && (counter < 4));
	 $display("Value read = %h",dut.first);
	 if (dut.first != (counter+15-2))
	   fail <= True;
	 dut.deq;
  endrule

  rule data_write1 ((counter >=4) && (counter < 6));
     dutput.put(counter+15);
  endrule

  rule clear_fifo (counter == 6);
	 dut.clear;
  endrule

  rule read1_value ((counter >=7) && (counter < 9));
     dutput.put(counter+25);
  endrule

  rule read_value2 ((counter >=9) && (counter < 11));
	 $display("Value read = %h",dut.first);
	 if (dut.first != (counter+25-2))
	   fail <= True;
	 dut.deq;
  endrule

  rule write_excess ((counter >=11) && (counter < 20));
     dutput.put(counter+6);
	 $display("Value Written = %h",(counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 22));
	 $display("Value read = %h",dut.first);
	 if (dut.first != (counter+6-9))
	   fail <= True;
	 dut.deq;
  endrule

  rule endofsim (counter == 22);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_FifoToPut 

endpackage : FifoToPut
