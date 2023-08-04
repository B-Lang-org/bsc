import StmtFSM::*;

typedef struct {
  Reg#(Bit#(32)) f1;
  Reg#(Bit#(32)) f2;
} S;

(* synthesize *)
module sysStmtFor_FieldUpd_Field();
   Reg#(Bit#(32)) rg_f1 <- mkReg('1);
   Reg#(Bit#(32)) rg_f2 <- mkReg('1);
   let rec = S { f1: rg_f1, f2: rg_f2 };

   Stmt s =
     seq
       for(rec.f1 <= 0; rec.f1 < 10; rec.f1 <= rec.f1 + 1) action
         $display("rec.f1 is %h", rec.f1);
       endaction
     endseq;

     mkAutoFSM(s);
endmodule
