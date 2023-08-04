import StmtFSM::*;

(* synthesize *)
module sysStmtFor();
   Reg#(Bit#(32)) rg_i <- mkReg('1);

   Stmt s =
     seq
       for(rg_i <= 0; rg_i < 10; rg_i <= rg_i + 1) action
         $display("rg_i is %h", rg_i);
       endaction
     endseq;

     mkAutoFSM(s);
endmodule
