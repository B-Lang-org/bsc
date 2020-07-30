import Vector::*;

interface Test;
   method ActionValue#(Bit#(32)) p1(Bit#(32) x);
   method ActionValue#(Bit#(32)) p2(Bit#(32) x);
endinterface

module mkTest(Test);
   method p1(x);
      actionvalue
	 $display("p1");
	 return(x);
      endactionvalue
   endmethod
   method p2(x);
      actionvalue
	 $display("p2");
	 return(x);
      endactionvalue
   endmethod
endmodule

(* synthesize *)
module sysIBMBug();
   
   Test pipe <- mkTest;
   
   rule test;
      Bit#(32) r1 <- primSeq(0,pipe.p1)(fromInteger(2));
      Bit#(32) r2 <- primSeq(0,pipe.p2)(fromInteger(4));
      $display("test: ", r1 + r2);
      $finish(0);
   endrule

endmodule
		    
		 

