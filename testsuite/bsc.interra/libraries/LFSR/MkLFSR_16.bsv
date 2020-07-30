package MkLFSR_16;
import LFSR::*;

module mkDesign_MkLFSR_16(LFSR#(Bit#(16)));

  LFSR#(Bit#(16)) dut();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_dut(dut);
  return dut;

endmodule: mkDesign_MkLFSR_16

function Bit#(16) next_value (Bit#(16) in_data,Bit#(16) pattern);
Bit#(16) value;
     if (in_data[0:0] == 1'b1) 
	    value = ((in_data >> 1) ^ pattern);
	 else
	    value = (in_data >> 1);
     return(value);
endfunction

module mkTestbench_MkLFSR_16();

  LFSR#(Bit#(16)) sr();
  mkLFSR_16 the_sr(sr);
  Reg#(Bit#(16)) counter <- mkReg(0);
  Reg#(Bit#(16)) exp_value <- mkReg(1);
  Reg#(Bit#(16)) exp_value1 <- mkReg(16'hABCD);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule shiftanddisplay (counter < 16);
     exp_value <= next_value(sr.value,16'h8016);
	 if (exp_value != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result (counter == 16);
      sr.seed('hABCD);
  endrule

  rule shiftanddisplay2 ((counter >= 17) && (counter < 33));
     exp_value1 <= next_value(sr.value,16'h8016);
	 if (exp_value1 != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value1,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result2 (counter == 33);
    if (fail)
	  $display("Simulation Failed");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule: mkTestbench_MkLFSR_16
endpackage: MkLFSR_16
