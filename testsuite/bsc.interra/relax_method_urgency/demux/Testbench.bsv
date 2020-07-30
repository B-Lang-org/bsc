import Design::*;

module mkTestbench();

// instantiating design
	IFC_design dut <- mkDesign;
	
	Reg#(Bit#(16)) counter <- mkReg(0);
// output checked for 16 cases
	rule count(counter < 16);
		counter <= counter + 1;
// action value method results stored in x0 etc
		let x0 <- dut.data_out_0;
		let x1 <- dut.data_out_1;
		let x2 <- dut.data_out_2;
		let x3 <- dut.data_out_3;
// display the output if actionvalue method corresponding to channel 0 is valid		
		if (x0 matches tagged Valid .v0)
		$display($time, "	Current Channel is 0 and O/p is %d",v0);
// display the output if actionvalue method corresponding to channel 1 is valid		
		if (x1 matches tagged Valid .v1)
		$display($time, "	Current Channel is 1 and O/p is %d",v1);
// display the output if actionvalue method corresponding to channel 2 is valid		
		if (x2 matches tagged Valid .v2)
		$display($time, "	Current Channel is 2 and O/p is %d",v2);
// display the output if actionvalue method corresponding to channel 3 is valid		
		if (x3 matches tagged Valid .v3)
		$display($time, "	Current Channel is 3 and O/p is %d",v3);
	endrule

// $finish after 16 cycles
	rule fin (counter==16);
		$finish(0);
	endrule
		
endmodule
