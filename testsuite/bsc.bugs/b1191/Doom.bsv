
interface ITest2_2;
  method ActionValue#(int) doStuff (int p1, int p2);
endinterface

(* synthesize *)
module mkTest2_2 (ITest2_2);
  Reg#(int) y2 <- mkReg (0);
  Reg#(int) z2 <- mkReg (0);

  method ActionValue#(int) doStuff (int p1, int p2) if (y2 == 5);
    z2 <= 3;
    return y2;
  endmethod

endmodule 
