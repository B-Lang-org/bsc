import ClientServer::*;
import GetPut::*;
import FIFO::*;
import Randomizable::*;
import StmtFSM::*;

import Divide::*;

(* synthesize *)
module sysTest_mkNonPipelinedDivider ();

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
    divideLower [i] <- mkNonPipelinedDivider (i+1);
  Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) divideFull [maxstages];
  for (Integer i = 0; i < maxstages; i = i + 1)
    divideFull [i] <- mkNonPipelinedDivider (i+1);

  Randomize #(Tuple2#(UInt#(m),UInt#(n))) rnd <- mkGenericRandomizer;

  Reg #(UInt #(32)) rg_in_num <- mkReg(numtests);
  Reg #(UInt #(32)) rg_out_num <- mkReg(0);
  FIFO #(Tuple2#(UInt#(m),UInt#(n))) ff_input <- mkSizedFIFO(valueOf(n)+4);
  
  function Tuple2#(UInt#(m),UInt#(n)) zeroUpperNumerator(Tuple2#(UInt#(m),UInt#(n)) in);
    match {.num, .den} = in;
    num = (num << valueOf(n)) >> valueOf(n); // Zero upper half.
    return tuple2(num,den);
  endfunction
  function Tuple2#(UInt#(m),UInt#(n)) noZeroDenominator(Tuple2#(UInt#(m),UInt#(n)) in);
    match {.num, .den} = in;
    if (den == 0) den = 1;
    return tuple2(num,den);
  endfunction

  rule start_div(rg_in_num < numtests);
    rg_in_num <= rg_in_num + 1;
    Tuple2#(UInt#(m),UInt#(n)) inp <- rnd.next ();
    inp = noZeroDenominator(inp);
    ff_input.enq(inp);
    for (Integer i = 0; i < maxstages; i = i + 1)
	divideLower [i] .request.put (zeroUpperNumerator(inp));
    for (Integer i = 0; i < maxstages; i = i + 1)
	divideFull [i] .request.put (inp);
  endrule
  rule finish_div(rg_out_num < numtests);
    rg_out_num <= rg_out_num + 1;
    match {.numA, .denA} = zeroUpperNumerator(ff_input.first);
    UInt#(n) q = (denA!=0) ? truncate(numA)/denA:0;
    UInt#(n) r = truncate(numA)%denA;
    for (Integer i = 0; i < maxstages; i = i + 1) begin
    match {.qt, .rt} <- divideLower [i] .response.get ();
    Bool passed = (qt == q && rt == r);
    if (passed) $display ("PASS");
    else $display ("iterations per cycle (%d) %h / %h = %h (vs. %h), rem %h (vs. %h) = FAIL",
	            i+1, numA, denA, qt, q, rt, r);
    end
    match {.numB, .denB} = ff_input.first;
    match {.qf, .rf} <- divideFull [0] .response.get ();
    for (Integer i = 1; i < maxstages; i = i + 1) begin
    match {.qt, .rt} <- divideFull [i] .response.get ();
    Bool passed = (qt == qf && rt == rf);
    if (passed) $display ("PASS");
    else $display ("iterations per cycle (%d) %h / %h = %h (vs. %h), rem %h (vs. %h) = FAIL",
	            i+1, numB, denB, qt, q, rt, r);
    end
    ff_input.deq();
  endrule

  method Action start if (rg_in_num >= numtests);
    rnd.cntrl.init ();
    rg_in_num <= 0;
  endmethod
  method done = (rg_out_num >= numtests);
  method waitTillDone if (rg_out_num >= numtests) = noAction;

endmodule
