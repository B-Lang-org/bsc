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

  //Exercise the properties syntax

  property exprTest;
    pipe1 > 3 && pipe2 == 0  or pipe2 == 0 |-> pipe1 == 0;
  endproperty

  property paramTest(x, y, z);
    x != y || x != z;
  endproperty

  property seqpropTest;
    paramTest(pipe1, pipe2, pipe3) or (pipe1 ##1 pipe2);
  endproperty

  property asgnTest;
    int x, y;
    UInt#(4) z;
    (x != y || x != z, z = 3);
  endproperty

  property binaryTest;
    exprTest or (exprTest and exprTest);
  endproperty

  property impTest(x, y);
    x == 0 |-> (x == 1 |=> y == 2);
  endproperty

  property ifTest;
    if (pipe1 > 0) impTest(p1, p2) else x == 0 |-> (x == 1 |=> y == 2);
  endproperty

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

module [Module] mkTest (Reg#(Int#(5)));

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
