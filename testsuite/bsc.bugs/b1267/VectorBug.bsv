package VectorBug;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface Test;
   interface Vector#(3, Reg#(Bit#(8))) zaz;
endinterface


(* synthesize *)
module mkTest0 (Test);

   Vector#(3, Reg#(Bit#(8))) reg_vector = newVector;
   
   for (Integer i = 0; i < 3; i = i + 1)
      begin
	 reg_vector[i] <- mkReg(0);
      end
   
   interface Vector zaz = reg_vector;
   
endmodule

(* synthesize *)
module mkTest1 (Test);

   Vector#(3, Reg#(Bit#(8))) reg_vector = ?;
   
   for (Integer i = 0; i < 3; i = i + 1)
      begin
	 reg_vector[i] <- mkReg(0);
      end
   
   interface Vector zaz = reg_vector;
   
endmodule


endpackage