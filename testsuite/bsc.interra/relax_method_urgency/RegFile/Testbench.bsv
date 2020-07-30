import Design::*;
import RegFile::*;

module mkTestbench();
// instantiate design
	IFC_design dut <- mkDesign;
	
	Reg#(Bit#(10)) count <- mkReg(0);
	Reg#(Bit#(18)) tmp <- mkReg(0);
// increment count	
	rule alway;
		count <= count + 1;
	endrule
// rules to update the data at various times
	rule al_1(count==0);
		$display($time, "	Updated Value: Data = %d", dut.update_reg(18'd0)); // updated value 0
	endrule

	rule al_2(count==1);
		$display($time, "	Updated Value: Data = %d", dut.update_reg(18'd10)); // updated value 10
	endrule

	rule al_3(count==2);
		$display($time, "	Updated Value: Data = %d", dut.update_reg(18'd100)); // updated value 100
	endrule

	rule al_4(count==3);
		$display($time, "	Updated Value: Data = %d", dut.update_reg(18'd1000)); // updated value 1000
	endrule

	rule al_5(count==4);
		$display($time, "	Updated Value: Data = %d", dut.update_reg(18'd10000));// updated value 10000
	endrule

	rule al_6(count==5);
		$display($time, "	Updated Value: Data = %d", dut.update_reg(18'd100000));// updated value 100000
	endrule

	rule al_7(count==6);
		$finish(0);
	endrule

endmodule
