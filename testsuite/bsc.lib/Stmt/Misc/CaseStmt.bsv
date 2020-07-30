import StmtFSM::*;

module sysCaseStmt();
   Reg#(int) rg <- mkReg(0);
   mkAutoFSM
      (seq
          case (mreg)
             0 : noAction;
             default : noAction;
          endcase
       endseq);
endmodule

