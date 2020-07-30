package DRegTest0;

import DReg::*;

(* synthesize *)
module sysDRegTest0 (Empty);
   
   Reg#(Bit#(3)) count <- mkReg(0);
   Reg#(Bit#(8)) test_count <- mkReg(0);
   Reg#(Bit#(8)) dreg0 <- mkDReg(3);
   Reg#(Bool)    dreg1 <- mkDRegU(False);
   
   rule every;
      count <= count + 1;
      if (count == 5)
	 begin
	    dreg0 <= {0, count};
	    test_count <= test_count + 1;
	 end
      else
	 dreg1 <= True;
      $display("(%5d) count = %0d dreg0 = %0d dreg1 = %b", $time, count, dreg0, dreg1);
      if (test_count == 5) $finish(0);
   endrule
   
   
endmodule


endpackage
