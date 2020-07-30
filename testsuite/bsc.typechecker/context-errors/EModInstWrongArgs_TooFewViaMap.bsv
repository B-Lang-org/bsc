import List::*;

module mkTest (a);
   List#(Reg#(a)) bs <- mapM(constFn(mkReg), upto(0,3));
   return bs[1];
endmodule

