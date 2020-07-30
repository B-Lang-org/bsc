import StmtFSM::*;

interface AVIfc;
   method ActionValue#(Bool) av();
endinterface

(* synthesize *)
module mkAV (AVIfc);
   Reg#(Bool) rg <- mkReg(True);
   method ActionValue#(Bool) av();
      rg <= !rg;
      return rg;
   endmethod
endmodule

(* synthesize *)
module mkTest ();
   AVIfc i <- mkAV;
   Vector#(2,Bool) bs;
   Stmt s = seq
               bs[0] <- i.av();
            endseq;
   mkFSM(s);
endmodule
