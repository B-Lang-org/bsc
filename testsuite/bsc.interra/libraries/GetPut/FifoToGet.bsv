package FifoToGet;

import GetPut :: *;
import FIFO :: *;

//mkDesign_FifoToGet to see if a proper verilog is generated.
module mkDesign_FifoToGet(Get #(Bit #(8) )); 
     FIFO#(Bit #(8)) f(); 
     mkFIFO the_f(f); 
     return (fifoToGet(f)); 
endmodule: mkDesign_FifoToGet


module mkTestbench_FifoToGet ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFO#(Bit#(8)) dut <- mkFIFO() ;
  Get #(Bit #(8)) dutget = fifoToGet (dut);
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(8)) count1 <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 2);
     dut.enq(counter+15);
  endrule

  rule read_value ((counter >=2) && (counter < 4));
	 Bit #(8) first <- dutget.get;
     $display("Value read = %h",first);
	 if (first != (counter+15-2))
	   fail <= True;
  endrule

  rule data_write1 ((counter >=4) && (counter < 6));
     dut.enq(counter+15);
  endrule

  rule clear_fifo (counter == 6);
	 dut.clear;
  endrule

  rule read1_value ((counter >=7) && (counter < 9));
     dut.enq(counter+25);
  endrule

  rule read_value2 ((counter >=9) && (counter < 11));
     Bit #(8) first <- dutget.get;
	 $display("Value read = %h",first);
	 if (first != (counter+25-2))
	   fail <= True;
  endrule

  rule write_excess ((counter >=11) && (counter < 20));
     dut.enq(counter+6);
	 $display("Value Written = %h",(counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 22));
     Bit #(8) first <- dutget.get;
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

endmodule: mkTestbench_FifoToGet


endpackage : FifoToGet
