import ClientServer::*;
import GetPut::*;
import Randomizable::*;
import StmtFSM::*;

import Divide::*;

(* synthesize *)
module sysTest_mkDivider ();

  TesterIfc #(7) tester4 <- mkTester (5, 64);

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
  provisos (Add#(n, n, m), Add#(1, m, TAdd#(n, a__)));

  Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) divideLower [maxstages];
  for (Integer i = 0; i < maxstages; i = i + 1)
    divideLower [i] <- mkDivider (i+1);
  Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) divideFull [maxstages];
  for (Integer i = 0; i < maxstages; i = i + 1)
    divideFull [i] <- mkDivider (i+1);

  Randomize #(Tuple2#(UInt#(m),UInt#(n))) rnd <- mkGenericRandomizer;

  Reg #(UInt #(32)) rg_test_num <- mkRegU;
  Reg #(Tuple2#(UInt#(m),UInt#(n))) rg_input <- mkRegU;
  
  function Tuple2#(UInt#(m),UInt#(n)) zeroUpperNumerator(Tuple2#(UInt#(m),UInt#(n)) in);
    match {.num, .den} = in;
    num = (num << valueOf(n)) >> valueOf(n); // Zero upper half.
    return tuple2(num,den);
  endfunction

  FSM fsm <- mkFSM (
    seq
      rnd.cntrl.init ();
      for (rg_test_num <= 0; rg_test_num < numtests; rg_test_num <= rg_test_num + 1) seq
	action
	  Tuple2#(UInt#(m),UInt#(n)) inp <- rnd.next ();
	  rg_input <= inp;
	  for (Integer i = 0; i < maxstages; i = i + 1)
	      divideLower [i] .request.put (zeroUpperNumerator(inp));
	  for (Integer i = 0; i < maxstages; i = i + 1)
	      divideFull [i] .request.put (inp);
	endaction
	action
	   match {.numA, .denA} = zeroUpperNumerator(rg_input);
	   UInt#(n) q = truncate(numA)/denA;
	   UInt#(n) r = truncate(numA)%denA;
	   for (Integer i = 0; i < maxstages; i = i + 1) begin
	      match {.qt, .rt} <- divideLower [i] .response.get ();
	      Bool passed = (qt == q && rt == r);
	      if (passed) $display ("PASS");
	      else $display ("iterations per cycle (%d) %h / %h = %h (vs. %h), rem %h (vs. %h) = FAIL",
			      i+1, numA, denA, qt, q, rt, r);
	   end
	   match {.numB, .denB} = rg_input;
	   match {.qf, .rf} <- divideFull [0] .response.get ();
	   for (Integer i = 1; i < maxstages; i = i + 1) begin
	      match {.qt, .rt} <- divideFull [i] .response.get ();
	      Bool passed = (qt == qf && rt == rf);
	      if (passed) $display ("PASS");
	      else $display ("iterations per cycle (%d) %h / %h = %h (vs. %h), rem %h (vs. %h) = FAIL",
			      i+1, numB, denB, qt, q, rt, r);
	   end
	endaction
      endseq
    endseq
  );

  method start = fsm.start;
  method done  = fsm.done;
  method waitTillDone = fsm.waitTillDone;

endmodule
