import StmtFSM::*;

(* synthesize *)
module sysAlwaysFSM_OneAction (Empty);

  // -----
  // Test mkAlwaysFSM with a sequence of one action

  // Include a state update
  // so that the action has associated clock and reset
  //
  Reg#(Bool) rg_b <- mkReg(False);

  Stmt seq_OneAction =
    seq
      action
        rg_b <= True;
        $display("Action");
      endaction
    endseq;

   mkAlwaysFSM(seq_OneAction);

   // -----
   // A separate proccess will finish the simulation
   // so that it doesn't run forever

   mkAutoFSM(seq
               delay(5);
	     endseq);

   // -----

endmodule
