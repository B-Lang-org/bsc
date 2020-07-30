import StmtFSM::*;

module sysCaseMatchesStmt();
   Reg#(Maybe#(int)) mreg <- mkReg(Invalid);
   mkAutoFSM
      (seq
          case (mreg) matches
             tagged Valid .y : noAction;
             tagged Invalid : noAction;
          endcase
       endseq);
endmodule

