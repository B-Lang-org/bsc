package Example;

import Zow::*;
import Vector::*;

(* synthesize *)
module mkExample (Empty);
   
   Reg#(Bool) zow <- mkDWire(False);
   
   Zow::mkZow;
   
   Vector#(3,Reg#(Bit#(5))) xx <- replicateM(mkRegU);
   
   Vector#(3,Reg#(Bit#(5))) ww <- replicateM(mkDWire(0));
   
   for (Integer i=0; i< 3; i=i+1)
      Reg#(Bool) z <- mkReg(False);
   
   for (Integer i=0; i< 3; i=i+1)
      begin

	 Reg#(Bool) x <- mkReg(False);
	 
	 for (Integer j=0; j< 3; j=j+1)
	    begin

	       Reg#(Bool) y <- mkReg(True);
	 
	       rule update;
		  y <= x;
	       endrule
	    end
      end

   
endmodule


endpackage