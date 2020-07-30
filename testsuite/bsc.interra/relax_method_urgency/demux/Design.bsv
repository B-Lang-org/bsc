// De-Multiplexer based switching of four channels :- In this De-Multiplexer there is a input stream which has to be De-multiplexed into four streams depending on select line. 

interface IFC_design;
	method ActionValue#(Maybe#(Bit#(4))) data_out_0;
	method ActionValue#(Maybe#(Bit#(4))) data_out_1;
	method ActionValue#(Maybe#(Bit#(4))) data_out_2;
	method ActionValue#(Maybe#(Bit#(4))) data_out_3;
endinterface
(*synthesize*)

module mkDesign (IFC_design);
	
	Reg#(Bit#(2)) select <- mkReg(0);
	Reg#(Bit#(16)) inp <- mkReg(16'hABCE);
	RWire#(Bit#(2)) sel_wire <- mkRWire;
	
// Channel selection is done within the module and the o.p channel is displayed
// Input incremented and displayed according to select bits
    rule always_fire;
		inp <= inp + 16'hA231;
		select <= select + 1;
    endrule

// wire set in rule	
	rule wire_set;
		sel_wire.wset(select);
    endrule

// wire read in method
	method ActionValue#(Maybe#(Bit#(4))) data_out_0 if (isValid(sel_wire.wget));
		if (validValue(sel_wire.wget)==0)
		begin
			$display("Channel 0 is Transferring");
			return tagged Valid inp[3:0]; // return the 4 relevant bits
		end
		else return Invalid;
	endmethod
	
// wire read in method
	method ActionValue#(Maybe#(Bit#(4))) data_out_1 if (isValid(sel_wire.wget));
		if (validValue(sel_wire.wget)==1)
		begin
			$display("Channel 1 is Transferring");
			return tagged Valid inp[7:4]; // return the 4 relevant bits
		end
		else return Invalid;
	endmethod
	
// wire read in method
	method ActionValue#(Maybe#(Bit#(4))) data_out_2 if (isValid(sel_wire.wget));
		if (validValue(sel_wire.wget)==2)
		begin
			$display("Channel 2 is Transferring");
			return tagged Valid inp[11:8]; // return the 4 relevant bits
		end
		else return Invalid;
	endmethod
	
// wire read in method
	method ActionValue#(Maybe#(Bit#(4))) data_out_3 if (isValid(sel_wire.wget));
		if (validValue(sel_wire.wget)==3)
		begin
			$display("Channel 3 is Transferring"); // return the 4 relevant bits
			return tagged Valid inp[15:12];
		end
		else return Invalid;
	endmethod
	
endmodule
