import StmtFSM::*;

(* synthesize *)
module sysStmtFor_RangeUpd();
   Reg#(Bit#(32)) rg_i <- mkReg('1);

   Stmt s =
     seq
       for(rg_i[7:0] <= 0; rg_i[7:0] < 10; rg_i[7:0] <= rg_i[7:0] + 1) action
         $display("rg_i is %h", rg_i);
       endaction
     endseq;

     mkAutoFSM(s);
endmodule
