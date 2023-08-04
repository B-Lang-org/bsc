import StmtFSM::*;
import Vector::*;

(* synthesize *)
module sysStmtFor_ArrayUpd_Elem();
   Reg#(Vector#(2, Bit#(32))) vec <- mkReg(replicate('1));

   Stmt s =
     seq
       for(vec[1] <= 0; vec[1] < 10; vec[1] <= vec[1] + 1) action
         $display("vec is %h", vec);
       endaction
     endseq;

     mkAutoFSM(s);
endmodule
