(* synthesize *)
module sysMethodConds_CaseAction ();

   Reg#(UInt#(2)) idx <- mkReg(0);
   Reg#(Bool) rg0 <- mkReg(False);
   Reg#(Bool) rg1 <- mkReg(False);
   Reg#(Bool) rg2 <- mkReg(False);
   Reg#(Bool) rg3 <- mkReg(False);

   rule r1;
      case (idx)
         0 : rg0 <= True;
         1 : rg1 <= True;
         2 : rg2 <= True;
         3 : rg3 <= True;
      endcase
   endrule

endmodule

