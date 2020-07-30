package MkPolyLFSR;
import LFSR::*;
import List::*;

module mkDesign_MkPolyLFSR(LFSR#(Bit#(64)));

  List #(Integer) my_list1 = Cons (7, Cons (3, Cons (2, Cons (1, Nil))));
  LFSR#(Bit#(64)) dut();
  mkPolyLFSR #(my_list1) the_dut(dut);
  return dut;

endmodule: mkDesign_MkPolyLFSR

function Bit#(64) next_value (Bit#(64) in_data,Bit#(8) pattern);
Bit#(64) value;
     if (in_data[0:0] == 1'b1) 
	    value = ((in_data >> 1) ^ {56'd0,pattern});
	 else
	    value = (in_data >> 1);
     return(value);
endfunction

module mkTestbench_MkPolyLFSR();

  List #(Integer) my_list1 = Cons (7, Cons (3, Cons (2, Cons (1, Nil))));
  LFSR#(Bit#(64)) sr();
  mkPolyLFSR #(my_list1) the_sr(sr);
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bit#(64)) exp_value <- mkReg(1);
  Reg#(Bit#(64)) exp_value1 <- mkReg(64'hABCDDEBAABCDDEBA);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule shiftanddisplay (counter < 64);
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

  rule test_result (counter == 64);
      sr.seed('hABCDDEBAABCDDEBA);
  endrule

  rule shiftanddisplay2 ((counter >= 65) && (counter < 129));
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

  rule test_result2 (counter == 129);
    if (fail)
	  $display("Simulation Failed");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule: mkTestbench_MkPolyLFSR

endpackage: MkPolyLFSR
