import StmtFSM::*;

typedef struct {
  Bit#(32) f1;
  Bit#(32) f2;
} Rec deriving (Bits);

(* synthesize *)
module sysStmtFor_FieldUpd_Reg();
   Reg#(Rec) rec <- mkReg(Rec { f1: '1, f2: '1});

   Stmt s =
     seq
       for(rec.f1 <= 0; rec.f1 < 10; rec.f1 <= rec.f1 + 1) action
         $display("rec is %h", rec);
       endaction
     endseq;

     mkAutoFSM(s);
endmodule
