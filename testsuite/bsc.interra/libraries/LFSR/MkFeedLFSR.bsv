package MkFeedLFSR;
import LFSR::*;

module mkDesign_MkFeedLFSR(LFSR#(Bit#(64)));

  LFSR#(Bit#(64)) dut();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_dut(dut);
  return dut;

endmodule: mkDesign_MkFeedLFSR

function Bit#(64) next_value (Bit#(64) in_data,Bit#(64) pattern);
Bit#(64) value;
     if (in_data[0:0] == 1'b1) 
	    value = ((in_data >> 1) ^ pattern);
	 else
	    value = (in_data >> 1);
     return(value);
endfunction

module mkTestbench_MkFeedLFSR();

  LFSR#(Bit#(64)) sr();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_sr(sr);
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(64)) exp_value <- mkReg(1);
  Reg#(Bit#(64)) exp_value1 <- mkReg(64'hABCDDEBAABCDDEBA);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule shiftanddisplay (counter < 64);
     exp_value <= next_value(sr.value,64'hDEADBEEFBADF00D);
	 if (exp_value != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result (counter == 64);
      sr.seed('hABCDDEBAABCDDEBA);
  endrule

  rule shiftanddisplay2 ((counter >= 65) && (counter < 129));
     exp_value1 <= next_value(sr.value,64'hDEADBEEFBADF00D);
	 if (exp_value1 != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value1,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result2 (counter == 129);
    if (fail)
	  $display("Simulation Failed");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule: mkTestbench_MkFeedLFSR
endpackage: MkFeedLFSR
