import List::*;

module mkTest ();
   List#(Reg#(Bool)) bs <- mapM(mkRegU,upto(0,3));
endmodule

