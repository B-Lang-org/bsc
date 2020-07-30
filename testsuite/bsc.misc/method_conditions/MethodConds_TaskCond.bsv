import Sub::*;

import "BDPI" function ActionValue#(Bool) getCond(Bool x);

(* synthesize *)
module sysMethodConds_TaskCond ();
   Ifc s <- mkUserSub;

   rule r;
      Bool c <- getCond(True);
      if (c) begin
         // there will be multiple COND signals assigned to the task result
         s.am1(0);
	 s.am2;
	 // and the task result is the condition of another task
	 $display("True");
      end
   endrule
endmodule

