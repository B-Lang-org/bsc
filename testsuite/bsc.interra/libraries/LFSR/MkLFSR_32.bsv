package MkLFSR_32;
import LFSR::*;

module mkDesign_MkLFSR_32(LFSR#(Bit#(32)));

  LFSR#(Bit#(32)) dut();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_dut(dut);
  return dut;

endmodule: mkDesign_MkLFSR_32

function Bit#(32) next_value (Bit#(32) in_data,Bit#(32) pattern);
Bit#(32) value;
     if (in_data[0:0] == 1'b1) 
	    value = ((in_data >> 1) ^ pattern);
	 else
	    value = (in_data >> 1);
     return(value);
endfunction

module mkTestbench_MkLFSR_32();

  LFSR#(Bit#(32)) sr();
  mkLFSR_32 the_sr(sr);
  Reg#(Bit#(32)) counter <- mkReg(0);
  Reg#(Bit#(32)) exp_value <- mkReg(1);
  Reg#(Bit#(32)) exp_value1 <- mkReg(32'hABCDDCBA);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule shiftanddisplay (counter < 32);
     exp_value <= next_value(sr.value,32'h80000057);
	 if (exp_value != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result (counter == 32);
      sr.seed('hABCDDCBA);
  endrule

  rule shiftanddisplay2 ((counter >= 33) && (counter < 65));
     exp_value1 <= next_value(sr.value,32'h80000057);
	 if (exp_value1 != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value1,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result2 (counter == 65);
    if (fail)
	  $display("Simulation Failed");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule: mkTestbench_MkLFSR_32
endpackage: MkLFSR_32
