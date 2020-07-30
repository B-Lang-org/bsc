package MkFifof;

import FIFOF::*;

(* synthesize *)
module mkDesign_MkFifof (FIFOF#(Bit #(8)));
  FIFOF#(Bit#(8)) datafifo <- mkFIFOF() ;
  return datafifo;
endmodule

module mkTestbench_MkFifof ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFOF#(Bit#(8)) datafifo <- mkDesign_MkFifof() ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write ((datafifo.notFull) && (counter < 20));
     datafifo.enq(8'h55);
	 $display("Cycle Number =%d, Value written = 55, FULL=%d, EMPTY=%d", counter, !datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule read_value ((datafifo.notEmpty) && ((counter > 20) && (counter < 40)));
	 $display("Cycle Number =%d, Value read = %h, FULL=%d, EMPTY=%d",counter, datafifo.first, !datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != 8'h55)
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write1 ((datafifo.notFull) &&  ((counter > 40) && (counter < 60)));
     datafifo.enq(counter+55);
	 $display("Cycle Number =%d, Value written = %h, FULL=%d, EMPTY=%d", counter, counter + 55, !datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule clear_fifo (counter == 60);
	 datafifo.clear;
	 $display("Cycle Number =%d, Clearing Fifo", counter);
  endrule

  rule data_write2 ((datafifo.notFull) &&  ((counter > 61) && (counter < 80)));
     datafifo.enq(8'haa);
	 $display("Cycle Number =%d, Value written = aa, FULL=%d, EMPTY=%d", counter, !datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule read_value2 ((datafifo.notEmpty) && ((counter > 80) && (counter < 100)));
	 $display("Cycle Number =%d, Value read = %h, FULL=%d, EMPTY=%d",counter, datafifo.first,!datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != 8'haa)
	   fail <= True;
	 datafifo.deq;
  endrule

 rule write_one (counter == 101);
     datafifo.enq(8'h50);
	 $display("Cycle Number = %d, Value Written = %h, FULL=%d, EMPTY=%d",counter, 8'h50,!datafifo.notFull, !datafifo.notEmpty);
  endrule

  rule write_one_read_one ((counter == 102));
     datafifo.enq(8'h60);
     datafifo.deq();
	 $display("Cycle Number = %d, Value Written = %h, FULL=%d, EMPTY=%d",counter, 8'h60,!datafifo.notFull, !datafifo.notEmpty);
	 $display("Cycle Number =%d, Value read = %h, FULL=%d, EMPTY=%d",counter, datafifo.first,!datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != 8'h50)
	   fail <= True;
  endrule

  rule read_value_last ((counter ==103));
	 $display("Cycle Number = %d,Value read = %h, FULL=%d, EMPTY=%d",counter, datafifo.first,!datafifo.notFull, !datafifo.notEmpty);
	 if (datafifo.first != 8'h60)
	   fail <= True;
	 datafifo.deq;
  endrule


  rule endofsim (counter == 105);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkFifof 
endpackage: MkFifof
