
import StmtFSM::*;
import Vector::*;

(* synthesize *)
module sysServerTestUpdate (Empty);

   // -----

   Reg#(UInt#(3)) idx <- mkRegU;

   Reg#(Bit#(10)) rg1 <- mkRegU;
   Reg#(Bit#(32)) rg2 <- mkRegU;

   function RStmt#(Bool) serverFn(Tuple2#(Bit#(10), Bit#(32)) v);
      match {.v1, .v2} = v;
      let s =
         seq
            action rg1 <= v1; rg2 <= v2; endaction
	    for (idx<=0; idx<6; idx<=idx+1)
	       seq
                  $display("Iteration: %d", idx);
		  action
                     $display("  Step 1: %d %d", rg1, rg2);
                     rg1 <= rg1 + 1;
                     rg2 <= rg2 + 2;
		  endaction
		  action
                     $display("  Step 2: %d %d", rg1, rg2);
                     rg1 <= rg1 + 1;
                     rg2 <= rg2 + 2;
		  endaction
	       endseq
	    return True;
	 endseq ;
      return s;
   endfunction

   FSMServer#(Tuple2#(Bit#(10), Bit#(32)), Bool) svr <- mkFSMServer(serverFn);

   // -----

   Vector#(2, Reg#(Bool)) results <- replicateM(mkReg(False));

   Stmt configSeq =
   (seq
       $display("Start vals: %d %d", results[0], results[1]);
       results[0] <- callServer(svr, tuple2(4, 'h00000000));
       results[1] <- callServer(svr, tuple2('h1A, 0));
       $display("End vals: %d %d", results[0], results[1]);
    endseq);

   mkAutoFSM(configSeq);

   // -----

endmodule

