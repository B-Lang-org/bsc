import Vector::*;

(* synthesize *)
module sysMethodConds_VecSelAction ();

   Reg#(UInt#(2)) idx <- mkReg(0);
   Reg#(Bool) rg0 <- mkReg(False);
   Reg#(Bool) rg1 <- mkReg(False);
   Reg#(Bool) rg2 <- mkReg(False);
   Reg#(Bool) rg3 <- mkReg(False);

   Vector#(4, Action) acts;
   acts[0] = action
                rg0 <= True;
             endaction;
   acts[1] = action
                rg1 <= True;
             endaction;
   acts[2] = action
                rg2 <= True;
             endaction;
   acts[3] = action
                rg3 <= True;
             endaction;

   rule r1;
      acts[idx];
   endrule

endmodule

