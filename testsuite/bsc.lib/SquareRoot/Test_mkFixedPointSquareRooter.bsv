import ClientServer::*;
import FixedPoint::*;
import GetPut::*;
import Randomizable::*;
import Real::*;
import StmtFSM::*;

import SquareRoot::*;

(* synthesize *)
module sysTest_mkFixedPointSquareRooter ();

  TesterIfc #(32, 32) tester1 <- mkTester (2, 10);
  TesterIfc #(48, 16) tester2 <- mkTester (2, 10);

  mkAutoFSM (seq
               $display ("Tester1 Start");
               tester1.start ();
	       tester1.waitTillDone ();
               $display ("Tester2 Start");
               tester2.start ();
	       tester2.waitTillDone ();
               $display ("Done");
	     endseq);
endmodule

interface TesterIfc #(numeric type isize, numeric type fsize);
  method Action start ();
  method Bool   done ();
  method Action waitTillDone ();
endinterface

module mkTester #(Integer maxstages, UInt #(32) numtests) (TesterIfc #(isize, fsize))
  provisos (
      Min#(isize, 1, 1),
      Add#(isize,fsize,m),
      Mul#(TDiv#(m, 2), 2, m),
      // per request of bsc
      Add#(a__, 1, TLog#(TAdd#(1, m)))
      );

  Server #(FixedPoint#(isize,fsize), Tuple2 #(FixedPoint#(isize,fsize), Bool)) srvrs [maxstages];
  for (Integer i = 0; i < maxstages; i = i + 1)
      srvrs [i] <- mkFixedPointSquareRooter (i+1);

  Randomize #(FixedPoint#(isize,fsize)) rnd <- mkGenericRandomizer;

  Reg #(UInt #(32)) rg_stages_num <- mkRegU;
  Reg #(UInt #(32)) rg_test_num <- mkRegU;
  Reg #(FixedPoint#(isize,fsize)) rg_input <- mkRegU;

  function Stmt doTest (Real x);
    return (seq
              action
	        FixedPoint#(isize,fsize) f = fromReal (x);
	        FixedPoint#(isize,fsize) sqrt_f = fromReal (sqrt (x));
                $write ("    sqrt(%h.%h) = (expected) %h.%h = (actual) ",
		        fxptGetInt (f),      fxptGetFrac (f),
		        fxptGetInt (sqrt_f), fxptGetFrac (sqrt_f));
	        srvrs [rg_stages_num] .request.put (fromReal (x));
              endaction
	      action
	        match .res <- srvrs [rg_stages_num] .response.get ();
	        let rt = tpl_1 (res);
	        let rounded = tpl_2 (res);
		$display ("%h.%h, %h", fxptGetInt (rt), fxptGetFrac (rt), rounded);
              endaction
	    endseq);
  endfunction

  let fsm_seq =
        seq
	  rnd.cntrl.init ();
	  for (rg_stages_num <= 0; rg_stages_num < fromInteger(maxstages); rg_stages_num <= rg_stages_num + 1) seq
	    $display ("  Testing %0d stage module", rg_stages_num + 1);

	    // Test some fixed values first
	    doTest (1);
	    doTest (2);
	    doTest (4);
	    doTest (10);
	    doTest ('h2000000);
	    doTest ('h3d80000);
	    doTest ('h3ef9db0);
	    doTest ('h3ffffff);
	    doTest ('h3ffc000);
	    doTest ('hfffe0000);
	    doTest (536870912.9375);
	    doTest (1073741824.96875);
	    doTest (0.5);
	    doTest (0.25);

            // Test random values
            for (rg_test_num <= 0; rg_test_num < numtests; rg_test_num <= rg_test_num + 1) seq
	      action
	        let inp <- rnd.next ();
		let abs_inp = ((inp < 0) ? -inp : inp);
	        rg_input <= abs_inp;
	        srvrs [rg_stages_num] .request.put (abs_inp);
	      endaction
	      action
	        match .res <- srvrs [rg_stages_num] .response.get ();
	        let rt = tpl_1 (res);
	        let rounded = tpl_2 (res);
	        let rt_sq = rt * rt;
	        let diff = rg_input - rt_sq;
		// XXX This check is too restrictive
	        Bool passed = (rounded ?
			       (diff < 1) && (diff > -1) :
			       (rg_input == rt_sq));
	        $display ("    sqrt (%h.%h) = %h.%h, %h = %s (diff = %h.%h)",
			  fxptGetInt (rg_input), fxptGetFrac (rg_input),
			  fxptGetInt (rt), fxptGetFrac (rt),
			  rounded,
			  (passed ? "PASS" : "FAIL"),
			  fxptGetInt (diff), fxptGetFrac (diff));
	      endaction
	    endseq  // for rg_test_num
	  endseq  // for rg_stagds_num
	endseq;

  FSM fsm <- mkFSM (fsm_seq);

  method start = fsm.start;
  method done  = fsm.done;
  method waitTillDone = fsm.waitTillDone;

endmodule
