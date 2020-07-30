import Design::*;

module mkTestbench();
// instantiating design	
	IFC_design dut <- mkDesign;
	
	Reg#(Bit#(16)) counter <- mkReg(0);

// checking for 16 cycles by incrementing counter
	rule count(counter < 16);
		counter <= counter + 1;
// calling the methods		
		dut.byte_0;
		dut.byte_1;
		dut.byte_2;
		dut.byte_3;
	endrule
// finish when appropriate cycles are over	
	rule fin (counter==16);
		$finish(0);
	endrule
		
endmodule
