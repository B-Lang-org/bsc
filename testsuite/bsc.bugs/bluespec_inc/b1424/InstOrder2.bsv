// We expect the rules to schedule in the order
// they are elaborated, but with submodules after
// the parent module (done, r2, r1).

import Clocks::*;

module mkInstOrder_Sub1();
   Reg#(Bool) rg1 <- mkReg(True);

   rule r1;
     rg1 <= !rg1;
     $display("Changing r1");
   endrule
endmodule

module mkInstOrder_Sub2();
   Reg#(Bool) rg2 <- mkReg(True);

   rule r2;
     rg2 <= !rg2;
     $display("Changing r2");
   endrule
endmodule

(* synthesize *)
module sysInstOrder2();
   Empty s2 <- mkInstOrder_Sub2();
   Empty s1 <- mkInstOrder_Sub1();

   Reg#(Bool) ready_to_finish <- mkReg(False);

   rule done;
      if (ready_to_finish) begin
	 $display("Exiting...");
	 $finish(0);
      end
      ready_to_finish <= True;
   endrule

endmodule
