import Vector::*;

interface MLM_IFC;
   method ActionValue#(Vector#(3,int)) maxlogmap2x2(int sigma_n);
endinterface

(* synthesize *)
module mkTb (Empty);
   MLM_IFC mlm <- mkMaxLogMap2x2;
endmodule

(* synthesize *)
module mkMaxLogMap2x2 (MLM_IFC);
 
function ActionValue#(Vector#(3,int)) fmaxlogmap2x2(int sigma_n);
  actionvalue
     Vector#(3,int) llr = replicate(0);
     llr[0] = 0;
     llr[1] = sigma_n;
     llr[2] = 0;
     return llr;
  endactionvalue
endfunction: fmaxlogmap2x2

method ActionValue#(Vector#(3,int)) maxlogmap2x2(int sigma_n);
   Vector#(3,int) llr <- fmaxlogmap2x2(sigma_n);
   return llr;
endmethod

endmodule: mkMaxLogMap2x2
