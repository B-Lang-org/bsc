package MkFifo1;

import FIFO::*;

(* synthesize *)
module mkDesign_MkFifo1 (FIFO #(Bit #(8)));
  FIFO#(Bit#(8)) datafifo <- mkFIFO1() ;
  return (datafifo);
endmodule

module mkTestbench_MkFifo1 ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFO#(Bit#(8)) datafifo <- mkDesign_MkFifo1() ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(8)) count1 <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 1);
     datafifo.enq(counter+15);
	 $display("Cycle Number =%d, Value written = %h",counter,counter+15);
  endrule

  rule read_value ((counter >=2) && (counter < 3));
	 $display("Cycle Number =%d, Value read = %h",counter,datafifo.first);
	 if (datafifo.first != (counter+15-2))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write1 ((counter >=3) && (counter < 4));
     datafifo.enq(counter+15);
	 $display("Cycle Number =%d, Value written = %h",counter,counter+15);
  endrule

  rule clear_fifo (counter == 4);
	 datafifo.clear;
	 $display("Cycle Number =%d, Clearing Fifo", counter);
  endrule

  rule read1_value ((counter >=5) && (counter < 6));
     datafifo.enq(counter+25);
	 $display("Cycle Number =%d, Value written = %h",counter,counter+25);
  endrule

  rule read_value2 ((counter >=6) && (counter < 7));
	 $display("Cycle Number =%d, Value read = %h",counter,datafifo.first);
	 if (datafifo.first != (counter+25-1))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule write_excess ((counter >=7) && (counter < 20));
     datafifo.enq(counter+6);
	 $display("Cycle Number =%d, Value Written = %h",counter, (counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 21));
	 $display("Cycle Number =%d, Value read = %h",counter, datafifo.first);
	 if (datafifo.first != (counter+6-13))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule endofsim (counter == 21);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkFifo1 
endpackage: MkFifo1
