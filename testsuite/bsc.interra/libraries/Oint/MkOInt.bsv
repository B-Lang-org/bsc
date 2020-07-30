package MkOInt;

import OInt ::*;
import ConfigReg ::*;

(* 
       always_ready ,
       always_enabled 
 *)

module mkDesign_MkOInt (Reg#(OInt#(32)));
  Reg#(OInt#(32)) data_reg <- mkReg(0);
  return data_reg;
endmodule: mkDesign_MkOInt

module mkTestbench_MkOInt();

  Reg#(OInt#(8)) data_reg <- mkReg(0);
  Reg#(Bit#(32)) counter <- mkReg(0);
  Reg#(Bit#(3)) count1 <- mkReg(1);
  Reg#(Bool) fail <- mkReg(False);


  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule write_data_reg (True);
	 count1 <= count1 + 1;
	 data_reg <= toOInt(count1);
  endrule

  rule check_result (True);
	 Bit#(3) val = fromOInt(data_reg);
	 //$display("One-hot Value read = %b Actual Value %d ",data_reg,val);
	 if ((val+1) != count1._read)
	    begin
	      $display("Mismatch Actual value = %h Exp value = %h",val,data_reg);
		  fail <= True;
	    end
  endrule

  rule nowend (counter == 20);
     if (fail)
	    $display("Simulation Failed");
	 else
	    $display("Simulation Passes");
     $finish(2'b00);
  endrule 
  
endmodule: mkTestbench_MkOInt
                 
endpackage: MkOInt






