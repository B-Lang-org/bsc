import ConfigReg::*;

interface IFC_prod;
   	method Action inp(Bool consReady);
	method ActionValue#(Bit#(8)) dataOut;
	method Bool prdReady; // send out status of producer
endinterface

(*synthesize*)

module producer(IFC_prod);
	
	Reg#(Bit#(8)) data <- mkConfigReg(5); // start with value 5
	Reg#(Bool) prodReady <- mkConfigReg(False); // default value is zero
	Reg#(Bool) consRdy <- mkConfigReg(?);

	rule always_fire;
		data <= data + 1; // produce data for producer to send out
	endrule

	rule inv_consRdy(!consRdy); // when consumer is not ready
		prodReady <= !prodReady;	
	endrule
	
	method ActionValue#(Bit#(8)) dataOut if(consRdy); // when consumer is ready
		prodReady <= True; // make producer ready
		$display($time,"	Producer Data is %d", data); // print the produced value
		return data;
	endmethod

	method Action inp(Bool consReady);
		consRdy <= consReady;
	endmethod
	
	method Bool prdReady;
		return prodReady; // send out status of producer
	endmethod
endmodule
