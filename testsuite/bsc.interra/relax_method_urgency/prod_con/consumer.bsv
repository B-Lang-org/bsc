import ConfigReg::*;

interface IFC_cons;
	method Action data_out(Bit#(8) data, Bool prdReady);
	method Bool cons_Ready; // indicates consumer is ready
endinterface

(*synthesize*)

module consumer(IFC_cons);

	Reg#(Bit#(8)) dataIn <- mkConfigReg(0);
	Reg#(Bool) consReady <- mkConfigReg(True);
	
	method Action data_out(Bit#(8) data, Bool prdReady);
		if(prdReady) // if producer is ready and has sent the data
			begin
        		dataIn <= data; // consume the data and print it out
				$display($time,"	Consumed Data is %d", dataIn);
            	consReady <= True;   // indicate value consumed
			end
        else 
			consReady <= False; // value not consumed when prdReady is false
	endmethod
	
	method Bool cons_Ready; // send out the status of consumer (ready or not)
		return consReady;
	endmethod
	
endmodule
