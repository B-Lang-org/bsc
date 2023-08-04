import StmtFSM::*;
import Vector::*;

(* synthesize *)
module sysStmtFor_ArrayUpd_Reg();
   Vector#(2, Reg#(Bit#(32))) vec <- replicateM(mkReg('1));

   Stmt s =
     seq
       for(vec[1] <= 0; vec[1] < 10; vec[1] <= vec[1] + 1) action
         $display("vec[1] is %h", vec[1]);
       endaction
     endseq;

     mkAutoFSM(s);
endmodule
