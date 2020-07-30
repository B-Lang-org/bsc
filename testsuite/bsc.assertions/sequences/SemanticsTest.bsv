import SVA::*;

interface Summer;
  method Action inp(int x);
  method int outp();
endinterface

module [Module] mkSimpleSummer (Summer);

  Reg#(int) pipe1 <- mkReg(0);
  Reg#(int) pipe2 <- mkReg(0);
  Reg#(int) pipe3 <- mkReg(0);
  Reg#(int) pipe4 <- mkReg(0);




  method Action inp(int x);
    int tmp = x;
    if (x < 0) tmp = tmp - 4;
      else tmp = tmp + 4;
    pipe1 <= tmp;
    pipe2 <= pipe1;
    pipe3 <= pipe2;
    pipe4 <= pipe3;
  endmethod

  method int outp();
    return pipe1 + pipe2 + pipe3 + pipe4;
  endmethod
endmodule

module [Module] sysSemanticsTest ();

  Summer sum <- mkSimpleSummer;
  Reg#(Int#(5)) r <- mkReg(0);
  Reg#(int) res <- mkReg(0);
  Reg#(int) oldres <- mkReg(0);
  Reg#(int) count <- mkReg(0);

  sequence initRes;
    ##1 res == 0 ##1 res == 4 ##1 res == 9 ##1 res == 15 ##1 True [*1:$];
  endsequence

  initial assert property (initRes) else $finish(0);

  sequence rCycles;
    (True [*1:$] ##1 r == -1 ##2 r == 1) [*1:$];
  endsequence

  initial assert property (rCycles) else $finish();

  sequence withinTest;
    True within initRes;
  endsequence

  sequence throughoutTest;
    True throughout initRes;
  endsequence

  initial assert property (withinTest) else $finish(1);

  initial assert property (throughoutTest) else $finish(1);

  initial assert property ((res > 0 ##1 res > 0) or (res > 0 ##1 res < 0)
                          or (res <= 0 ##1 res <= 0)or (res <= 0 ##1 res == 0)) else $finish();

  rule gogo(True);
    r <= r + 1;
    count <= count + 1;
    sum.inp(signExtend(r));

    res <= sum.outp();
    oldres <= res;
    $display("Res: %0d", res);
  endrule

  rule endTest (count > 100);
    $finish(0);
  endrule

endmodule
