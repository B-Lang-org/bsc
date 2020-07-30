import RegFile::*;

// method to update register
interface IFC_design;
	method ActionValue#(Bit#(18)) update_reg(Bit#(18) dat);
endinterface

(* synthesize *)

module mkDesign (IFC_design);

// Instantiating Regfile
	RegFile#(Bit#(3),Bit#(18)) dut <- mkRegFile(3'b0,3'b111);
	RWire#(Bit#(18)) dout_w <- mkRWire;
// wire set in rule  	
	rule display;
		dout_w.wset(dut.sub(3'b0)); // regfile read
    endrule

// wire read in method  	
	method ActionValue#(Bit#(18)) update_reg(Bit#(18) dat) if(isValid(dout_w.wget)) ;
		$display ($time,"	To be written: Data = %d", dat);
		dut.upd(3'b0, dat); // regfile updated
		return validValue(dout_w.wget);
	endmethod

endmodule


