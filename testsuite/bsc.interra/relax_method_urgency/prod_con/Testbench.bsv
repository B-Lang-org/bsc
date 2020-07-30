import ConfigReg::*;
import producer::*; // import producer and consumer designs
import consumer::*;

interface IFC_top;
	method Action consumer_display; // method to display data going to consumer
endinterface

module mkTestbench(IFC_top);

//	Instantiating Design
	IFC_prod prod <- producer; // instantiate producer
	IFC_cons cons <- consumer; // instantiate consumer
	
	RWire#(Bit#(8)) data_2_cons <- mkRWire;
	Reg#(Bit#(5)) counter <- mkConfigReg(0);
	
	rule prod_inp(counter < 15);
		prod.inp(cons.cons_Ready); // connect producer input to consumer ready signal
	endrule
	
// test for 15 cycles
	rule cnt_2_15(counter < 15);
		let x <- prod.dataOut; // get producer data 
		cons.data_out( x, prod.prdReady); // send data to consumer along with the producer ready signal
		data_2_cons.wset(x); // set wire to send producer data to consumer
		counter <= counter + 1; 
	endrule

// finish after 15 cycles	
	rule count_end(counter==15);
		$finish(0);
	endrule

//	define method to display data going to consumer 
	method Action consumer_display if(isValid(data_2_cons.wget));
		$display("The Data being sent from top to Consumer %d",validValue(data_2_cons.wget));
	endmethod

endmodule
