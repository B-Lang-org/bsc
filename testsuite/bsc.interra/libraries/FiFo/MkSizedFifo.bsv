package MkSizedFifo;

import FIFO::*;

(* synthesize *)
module mkDesign_MkSizedFifo (FIFO#(Bit #(8)));
  FIFO#(Bit#(8)) datafifo <- mkSizedFIFO(16) ;
  return (datafifo);
endmodule

module mkTestbench_MkSizedFifo ();
        
  FIFO#(Bit#(8)) datafifo <- mkDesign_MkSizedFifo ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 16);
     datafifo.enq(counter+15);
	 $display("Cycle Number = %d Value Written = %h",counter,counter + 15);
  endrule

  rule read_value ((counter >=16) && (counter < 32));
	 $display("Cycle Number = %d, Value read = %h",counter,datafifo.first);
	 if (datafifo.first != (counter+15-16))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write1 ((counter >=32) && (counter < 48));
     datafifo.enq(counter+15);
	 $display("Cycle Number = %d Value Written = %h",counter,counter + 15);
  endrule

  rule clear_fifo (counter == 48);
	 datafifo.clear;
	 $display("Cycle Number = %d Clearing FIFO",counter);
  endrule

  rule read1_value ((counter >=49) && (counter < 65));
     datafifo.enq(counter - 49 );
	 $display("Cycle Number = %d Value Written = %h",counter,counter - 49);
  endrule

  rule read_value2 ((counter >= 8'd65) && (counter < 8'd81));
	 $display("Cycle Number = %d Value read = %h",counter,datafifo.first);
	 if (datafifo.first != (counter-65))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule write_excess ((counter >=81) && (counter < 111));
     datafifo.enq(counter);
	 $display("Cycle Number = %d, Value Written = %h",counter, counter);
  endrule

  rule read_value_excess ((counter >=111) && (counter < 128));
	 $display("Cycle Number = %d, Value read = %h",counter,datafifo.first);
	 if (datafifo.first != (counter-30))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write2 ((counter >=128) && (counter < 133));
     datafifo.enq(counter-128);
	 $display("Cycle Number = %d, Value Written = %h",counter, counter-128);
  endrule

  rule data_read2 ((counter >=133) && (counter < 138));
	 $display("Cycle Number = %d Value read = %h",counter,datafifo.first);
	 $display("Cycle Number = %d Value written = %h",counter,counter);
	 if (datafifo.first != (counter-133))
	   fail <= True;
	 datafifo.deq;
     datafifo.enq(counter);
  endrule

  rule endofsim (counter == 138);
	if (fail)
	  $display("counter = %d Simulation Fails",counter);
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkSizedFifo 
endpackage: MkSizedFifo
