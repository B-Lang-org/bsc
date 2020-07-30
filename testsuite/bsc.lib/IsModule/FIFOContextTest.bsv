import FIFO::*;
import ModuleContext::*;

module [ModuleContext#(Integer)] mkIncrFIFO (FIFO#(Bit#(32)));

 let n <- getContext();
 let q <- mkSizedFIFO(n);
 putContext(n + 1);
 return q;

endmodule

module [ModuleContext#(Integer)] mkFIFOTester ();

 let q1 <- mkIncrFIFO();
 let q2 <- mkIncrFIFO();
 let q3 <- mkIncrFIFO();

endmodule

module [ModuleContext#(Integer)] mkTesterTester ();


 let t1 <- mkFIFOTester();
 let t2 <- mkFIFOTester();

endmodule

(* synthesize *)
module [Module] mkFIFOContextTest();

 match {.final_s, .foo} <- runWithContext(1, mkTesterTester);

 messageM(strConcat("Final state was: ", integerToString(final_s)));

 rule print (True);

     $display("I love the number %0d", fromInteger(final_s));

 endrule

endmodule