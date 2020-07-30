package MkLFSR_8;
import LFSR::*;

module mkDesign_MkLFSR_8(LFSR#(Bit#(8)));

  LFSR#(Bit#(8)) dut();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_dut(dut);
  return dut;

endmodule: mkDesign_MkLFSR_8

function Bit#(8) next_value (Bit#(8) in_data,Bit#(8) pattern);
Bit#(8) value;
     if (in_data[0:0] == 1'b1) 
	    value = ((in_data >> 1) ^ pattern);
	 else
	    value = (in_data >> 1);
     return(value);
endfunction

module mkTestbench_MkLFSR_8();

  LFSR#(Bit#(8)) sr();
  mkLFSR_8 the_sr(sr);
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(8)) exp_value <- mkReg(1);
  Reg#(Bit#(8)) exp_value1 <- mkReg(8'hAB);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule shiftanddisplay (counter < 8);
     exp_value <= next_value(sr.value,8'h8E);
	 if (exp_value != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result (counter == 8);
      sr.seed('hAB);
  endrule

  rule shiftanddisplay2 ((counter >= 9) && (counter < 17));
     exp_value1 <= next_value(sr.value,8'h8E);
	 if (exp_value1 != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value1,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result2 (counter == 17);
    if (fail)
	  $display("Simulation Failed");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule: mkTestbench_MkLFSR_8
endpackage: MkLFSR_8
