package DRegTest1;

import DReg::*;
import Vector::*;

(* synthesize *)
module sysDRegTest1 (Empty);
   
   Reg#(Bit#(3)) count <- mkReg(0);
   Reg#(Bit#(8)) test_count <- mkReg(0);   
   Vector#(5, Reg#(Bool)) dreg_vector <- replicateM(mkDReg(False));
   
   let dreg0 = dreg_vector[0];
   let dreg1 = dreg_vector[1];
   let dreg2 = dreg_vector[2];
   let dreg3 = dreg_vector[3];
   let dreg4 = dreg_vector[4];
   
   for (Integer x = 1; x < 5; x = x + 1)
      begin
	 rule connect;
	    let prev = dreg_vector[x-1];
	    (dreg_vector[x]) <= prev;
	 endrule
	 
      end

   
   rule every;
      count <= count + 1;
      if (count == 5)
	 begin
	    (dreg_vector[0]) <= True;
	    test_count <= test_count + 1;
	 end
      $display("(%5d) count = %0d dreg0 = %b dreg1 = %b dreg2 = %b dreg3 = %b dreg4 = %b", 
	 $time, count, dreg0, dreg1, dreg2, dreg3, dreg4);
      if (test_count == 5) $finish(0);
   endrule
   
   
endmodule


endpackage
