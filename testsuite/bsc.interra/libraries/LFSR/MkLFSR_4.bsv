package MkLFSR_4;
import LFSR::*;

module mkDesign_MkLFSR_4(LFSR#(Bit#(4)));

  LFSR#(Bit#(4)) dut();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_dut(dut);
  return dut;

endmodule: mkDesign_MkLFSR_4

function Bit#(4) next_value (Bit#(4) in_data,Bit#(4) pattern);
Bit#(4) value;
     if (in_data[0:0] == 1'b1) 
	    value = ((in_data >> 1) ^ pattern);
	 else
	    value = (in_data >> 1);
     return(value);
endfunction

module mkTestbench_MkLFSR_4();

  LFSR#(Bit#(4)) sr();
  mkLFSR_4 the_sr(sr);
  Reg#(Bit#(4)) counter <- mkReg(0);
  Reg#(Bit#(4)) exp_value <- mkReg(1);
  Reg#(Bit#(4)) exp_value1 <- mkReg(4'hA);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule shiftanddisplay (counter < 4);
     exp_value <= next_value(sr.value,4'h9);
	 if (exp_value != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result (counter == 4);
      sr.seed('hA);
  endrule

  rule shiftanddisplay2 ((counter >= 5) && (counter < 9));
     exp_value1 <= next_value(sr.value,4'h9);
	 if (exp_value1 != sr.value)
	   begin
         $display("Mismatch counter = %d Exp = %h Actual = %h",counter,exp_value1,sr.value); 
         fail <= True;
	   end
	 else
       $display("Data Matched counter = %d Value = %h",counter,sr.value); 
	 sr.next;
  endrule

  rule test_result2 (counter == 9);
    if (fail)
	  $display("Simulation Failed");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule: mkTestbench_MkLFSR_4
endpackage: MkLFSR_4
