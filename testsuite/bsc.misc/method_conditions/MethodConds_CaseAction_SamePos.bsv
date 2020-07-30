(* synthesize *)
module sysMethodConds_CaseAction_SamePos ();

   Reg#(UInt#(2)) idx <- mkReg(0);
   Reg#(Bool) rg0 <- mkReg(False);
   Reg#(Bool) rg1 <- mkReg(False);
   Reg#(Bool) rg2 <- mkReg(False);
   Reg#(Bool) rg3 <- mkReg(False);

   function Reg#(Bool) rg();
      case (idx)
         0 : return rg0;
         1 : return rg1;
         2 : return rg2;
         default : return rg3;
      endcase
   endfunction

   rule r1;
      rg() <= True;
   endrule

endmodule

