import ClientServer::*;
import GetPut::*;
import Randomizable::*;
import StmtFSM::*;

import SquareRoot::*;

(* synthesize *)
module sysTest_mkSquareRooter ();

  TesterIfc #(32) tester4 <- mkTester (2, 10);

  mkAutoFSM (seq
               tester4.start ();
	       tester4.waitTillDone ();
               $display ("Done");
	     endseq);
endmodule


interface TesterIfc #(numeric type n);
  method Action start ();
  method Bool   done ();
  method Action waitTillDone ();
endinterface

module mkTester #(Integer maxstages, UInt #(32) numtests) (TesterIfc #(n))
  provisos (Mul#(TDiv#(n, 2), 2, n));

  Server #(UInt #(n), Tuple2 #(UInt #(n), Bool)) srvrs [maxstages];
  for (Integer i = 0; i < maxstages; i = i + 1)
    srvrs [i] <- mkSquareRooter (i+1);

  Randomize #(UInt #(n)) rnd <- mkGenericRandomizer;

  Reg #(UInt #(32)) rg_test_num <- mkRegU;
  Reg #(UInt #(n)) rg_input <- mkRegU;

  FSM fsm <- mkFSM (seq
                      rnd.cntrl.init ();
                      for (rg_test_num <= 0; rg_test_num < numtests; rg_test_num <= rg_test_num + 1) seq
		        action
			  let inp <- rnd.next ();
			  rg_input <= inp;
			endaction
		        srvrs [0] .request.put (rg_input);
			action
			   match .res <- srvrs [0] .response.get ();
			   let rt = tpl_1 (res);
			   let rounded = tpl_2 (res);
			   let rt_sq = rt * rt;
			   let rt_plus1_sq = (rt + 1) * (rt + 1);
			   Bool passed = (rounded ?
			                    (rg_input > rt_sq) &&
					        // the next square might roll over
					        ((rt_plus1_sq <= rt_sq) || (rg_input < rt_plus1_sq)) :
					    (rg_input == rt_sq));
			   $display ("sqrt (%h) = %h, %h = %s", rg_input, rt, rounded,
			             (passed ? "PASS" : "FAIL"));
			endaction
		      endseq
                    endseq);

  method start = fsm.start;
  method done  = fsm.done;
  method waitTillDone = fsm.waitTillDone;

endmodule
