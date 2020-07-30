package MkFifo;

import FIFO::*;

(* synthesize *)
module mkDesign_MkFifo (FIFO#(Bit #(8)));
  FIFO#(Bit#(8)) datafifo <- mkFIFO() ;
  return (datafifo);
endmodule

/*            
interface Design_IFC;
    method Action push(Bit#(8) data_in);
    method Action pop();
    method Bit#(8) data_out();
    method Bool overflow();
    method Bool underflow();
endinterface: Design_IFC
*/

module mkTestbench_MkFifo ();
        
  Reg#(Bit#(8)) sizeoflist <- mkReg(0);
  FIFO#(Bit#(8)) datafifo <- mkDesign_MkFifo() ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(8)) count1 <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 2);
     datafifo.enq(counter+15);
	 $display("Cycle Number = %d, Value written = %h",counter, counter + 15);
  endrule

  rule read_value ((counter >=2) && (counter < 4));
	 $display("Cycle Number = %d, Value read = %h",counter, datafifo.first);
	 if (datafifo.first != (counter+15-2))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule data_write1 ((counter >=4) && (counter < 6));
     datafifo.enq(counter+15);
	 $display("Cycle Number = %d, Value written = %h",counter, counter + 15);
  endrule

  rule clear_fifo (counter == 6);
	 datafifo.clear;
	 $display("Cycle Number = %d, Clearing FIFO",counter);
  endrule

  rule read1_value ((counter >=7) && (counter < 9));
     datafifo.enq(counter+25);
	 $display("Cycle Number = %d, Value written = %h",counter, counter + 25);
  endrule

  rule read_value2 ((counter >=9) && (counter < 11));
	 $display("Cycle Number = %d, Value read = %h",counter, datafifo.first);
	 if (datafifo.first != (counter+25-2))
	   fail <= True;
	 datafifo.deq;
  endrule

  rule write_excess ((counter >=11) && (counter < 20));
     datafifo.enq(counter+6);
	 $display("Cycle Number = %d, Value Written = %h",counter,(counter+6));
  endrule

  rule read_value_excess ((counter >=20) && (counter < 22));
	 $display("Cycle Number =%d, Value read = %h",counter, datafifo.first);
	 if (datafifo.first != (counter+6-9))
	   fail <= True;
	 datafifo.deq;
  endrule

 rule write_one (counter == 22);
     datafifo.enq(8'h50);
	 $display("Cycle Number = %d, Value Written = %h",counter, 8'h50);
  endrule

  rule write_one_read_one ((counter == 23));
     datafifo.enq(8'h60);
     datafifo.deq();
	 $display("Cycle Number = %d, Value Written = %h",counter, 8'h60);
	 $display("Cycle Number =%d, Value read = %h",counter, datafifo.first);
	 if (datafifo.first != 8'h50)
	   fail <= True;
  endrule

  rule read_value_last ((counter ==24));
	 $display("Cycle Number = %d,Value read = %h",counter, datafifo.first);
	 if (datafifo.first != 8'h60)
	   fail <= True;
	 datafifo.deq;
  endrule


  rule endofsim (counter == 25);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule

endmodule: mkTestbench_MkFifo 
endpackage: MkFifo
