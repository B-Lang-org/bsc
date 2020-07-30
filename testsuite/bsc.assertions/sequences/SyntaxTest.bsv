import SVA::*;

interface Summer;
  method Action inp(int x);
  method int outp();
endinterface

module [Module] mkSimpleSummer (Summer);

  Reg#(int) pipe1();
  mkReg#(0) i_pipe1(pipe1);
  Reg#(int) pipe2 <- mkReg(0);
  Reg#(int) pipe3 <- mkReg(0);
  Reg#(int) pipe4 <- mkReg(0);

  //Exercise the sequence syntax

  sequence exprTest;
    pipe1 > 3 && pipe2 < 4 && pipe3 != 5 && pipe4 == pipe4;
  endsequence

  sequence varTest;
    int x, y;
    UInt#(4) z;
    x != y || x != z;
  endsequence

  sequence asgnTest;
    int x, y;
    UInt#(4) z;
    (x != y || x != z, z = 3);
  endsequence

  sequence concatTest;
    pipe1 == 0 ##0 pipe2 == 0 ##1 pipe3 == 0 ##2 pipe4 == 0 ##3 pipe1 == 0;
  endsequence

  sequence unaryConcat;
    ##5 pipe1 == 0 ##111 pipe2 == 0;
  endsequence

  sequence rangeTest;
    pipe1 == 0 ##[10:55] pipe1 == 0;
  endsequence

  sequence unboundTest;
    pipe1 == 0 ##[0:$] pipe2 == 0;
  endsequence

  sequence repTest;
    pipe1 == 0 [*5] ##5 pipe2 == 0 [*5:$];
  endsequence

  sequence nonConsec;
    pipe1 > 5 [= 12] ##1 pipe2 [=1:$];
  endsequence

  sequence gotoTest;
    pipe1 == 4 [-> 5];
  endsequence

  sequence binaryTest;
    repTest() or gotoTest() and unboundTest() intersect nonConsec() within unaryConcat() throughout concatTest();
  endsequence

  sequence firstMatchTest;
    int x;
    first_match(gotoTest) or first_match(binaryTest, x = 4);
  endsequence

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

module [Module] sysSyntaxTest (Reg#(Int#(5)));

  Summer sum <- mkSimpleSummer;
  Reg#(Int#(5)) r <- mkReg(0);

  rule gogo(True);
  r <= r + 5;
  sum.inp(zeroExtend(r));

  int res = sum.outp();
  $display("Res: %0d", res);
  endrule

  method Int#(5) _read;
    return r;
  endmethod

  method Action _write(Int#(5) x);
    r <= x;
  endmethod
endmodule
