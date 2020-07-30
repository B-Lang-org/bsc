package Example;

//import Zow::*;
import Vector::*;

(* synthesize *)
module sysExample (Empty);
   
   Reg#(Bool) zow <- mkDWire(False);
   
   mkZow;
   
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



module mkZow (Empty);
   
   Reg#(Bool) zow2 <- mkReg(False);
   
endmodule


endpackage
