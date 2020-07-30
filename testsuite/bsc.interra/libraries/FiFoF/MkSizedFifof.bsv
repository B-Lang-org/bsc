package MkSizedFifof;

import FIFOF::*;

(* synthesize *)
module mkDesign_MkSizedFifof (FIFOF#(Bit #(8)));
  FIFOF#(Bit#(8)) datafifo <- mkSizedFIFOF(16) ;
  return (datafifo);
endmodule

module mkTestbench_MkSizedFifof ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFOF#(Bit#(8)) datafifo <- mkDesign_MkSizedFifof() ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 20);
     datafifo.enq(counter);
	 $display("Cycle Number =%d, Value written = %h, Full =%d, Empty =%d",counter, counter, !datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule read_value (counter > 20 && counter < 40);
	 $display("Cycle Number =%d, Value read = %h, Full =%d, Empty =%d",counter,datafifo.first, !datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != (counter -21))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write1 ((counter > 40) && (counter < 60));
     datafifo.enq(counter+55);
	 $display("Cycle Number =%d, Value written = %h, Full =%d, Empty =%d",counter, counter+55, !datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule clear_fifo (counter == 60);
	 datafifo.clear;
	 $display("Cycle Number =%d, Clearing Buffer",counter);
  endrule

  rule data_write2 (counter > 61 && counter < 80);
     datafifo.enq(counter - 62);
	 $display("Cycle Number =%d, Value written = %h, Full =%d, Empty =%d",counter, counter-62, !datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule read_value2 (counter > 80 && counter < 100);
	 $display("Cycle Number =%d, Value read = %h, Full =%d, Empty =%d",counter,datafifo.first, !datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != (counter - 81))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_writeone (counter == 100);
     datafifo.enq(counter);
	 $display("Cycle Number =%d, Value written = %h, Full =%d, Empty =%d",counter, counter, !datafifo.notFull, !datafifo.notEmpty);
  endrule
  
  rule data_writeread (counter > 100);
     datafifo.enq(counter);
     datafifo.deq();
	 $display("Cycle Number =%d, Value written = %h, Full =%d, Empty =%d",counter, counter, !datafifo.notFull, !datafifo.notEmpty);
	 $display("Cycle Number =%d, Value read = %h, Full =%d, Empty =%d",counter,datafifo.first, !datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != (counter-1))
	   fail <= True;
  endrule

  rule endofsim (counter == 150);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkSizedFifof 
endpackage: MkSizedFifof
