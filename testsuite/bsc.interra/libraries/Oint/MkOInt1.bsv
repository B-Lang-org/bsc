package MkOInt1;

import OInt ::*;
import List ::*;
import ConfigReg ::*;

(* 
       always_ready ,
       always_enabled 
 *)

module mkDesign_MkOInt1 (Reg#(OInt#(32)));
  Reg#(OInt#(32)) data_reg <- mkReg(0);
  return data_reg;
endmodule: mkDesign_MkOInt1

module mkTestbench_MkOInt1();

  Reg#(OInt#(8)) data_reg <- mkReg(0);
  Reg#(OInt#(8)) data_reg1 <- mkReg(0);
  Reg#(Bit#(32)) counter <- mkReg(0);
  Reg#(Bit#(3)) count1 <- mkReg(1);
  Reg#(Bool) fail <- mkReg(False);

  List#(Maybe#(Tuple4#(Bit#(8), Bit#(1), Bit#(1) , Bit#(8)))) test ;
       test = Cons( Valid (tuple4 (8'b10101010,1'b1,1'b0,8'b01010101)),
              Cons( Valid (tuple4 (8'b10101010,1'b1,1'b1,8'b01010101)),
              Cons( Valid (tuple4 (8'b10001010,1'b0,1'b1,8'b00010101)),
              Cons( Valid (tuple4 (8'b10001010,1'b0,1'b0,8'b00010100)),
              Cons( Valid (tuple4 (8'b01110011,1'b1,1'b1,8'b10111001)),
              Cons( Valid (tuple4 (8'b11001100,1'b0,1'b0,8'b10011000)),
              Cons( Valid (tuple4 (8'b10001000,1'b0,1'b0,8'b00010000)),
              Cons( Invalid, Nil)))))))) ;

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule write_data_reg (True);
	 count1 <= count1 + 1;
	 data_reg <= toOInt(count1);
	 data_reg1 <= toOInt(count1);
  endrule

  rule check_result (True);
	 if (data_reg != data_reg1)
	    begin
	      $display("Mismatch Actual value = %h Exp value = %h",data_reg,data_reg1);
		  fail <= True;
	    end
  endrule

  rule check_result2 (True);
    case (List:: select(test,data_reg)) matches
      tagged Invalid :
         begin
           if (fail)
	          $display("Simulation Failed");
	       else
	          $display("Simulation Passes");
           $finish(2'b00);
         end
      tagged Valid ({.x,.y,.z,.res}) :
         begin
	          $display("List Read : %b %b %b %b",x,y,z,res);
         end
    endcase 
  endrule

endmodule: mkTestbench_MkOInt1
                 
endpackage: MkOInt1






