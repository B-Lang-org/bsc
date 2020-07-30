// Different Bytes read from 64 bit data according to byte selection bits

interface IFC_design;
	method Action byte_0;
	method Action byte_1;
	method Action byte_2;
	method Action byte_3;
endinterface
(*synthesize*)

module mkDesign (IFC_design);
	
	Reg#(Bit#(2)) be_reg <- mkReg(0);
	Reg#(Bit#(64)) reg_64 <- mkReg(64'hA2143B43C423001);
	RWire#(Bit#(2)) byte_en <- mkRWire;
// byte_en signal generated in the module itself	
    rule always_fire;
		reg_64 <= reg_64 + 64'hA7FFF1117747457;
		be_reg <= be_reg + 1;
    endrule
// wire set in rule	
	rule wire_set;
		byte_en.wset(be_reg);
    endrule

// wire read in method 0	
	method Action byte_0 if (isValid(byte_en.wget));
		if (validValue(byte_en.wget)==0)
			$display("Reading Bytes 0 and 1 %d",reg_64[15:0]);
	endmethod
	
// wire read in method 1	
	method Action byte_1 if (isValid(byte_en.wget));
		if (validValue(byte_en.wget)==1)
			$display("Reading Byte 2 and 3 %d",reg_64[31:16]);
	endmethod
	
// wire read in method 2	
	method Action byte_2 if (isValid(byte_en.wget));
		if (validValue(byte_en.wget)==2)
			$display("Reading Byte 4 and 5 %d",reg_64[47:32]);
	endmethod
	
// wire read in method 3	
	method Action byte_3 if (isValid(byte_en.wget));
		if (validValue(byte_en.wget)==3)
			$display("Reading Byte 6 and 7 %d",reg_64[63:48]);
	endmethod
	
endmodule
