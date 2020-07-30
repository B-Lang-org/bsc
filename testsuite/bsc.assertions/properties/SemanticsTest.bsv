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

(*synthesize*)
module [Module] sysSemanticsTest ();

  Summer sum <- mkSimpleSummer;
  Reg#(Int#(5)) r <- mkReg(0);
  Reg#(int) res <- mkReg(0);
  Reg#(int) oldres <- mkReg(0);
  Reg#(int) count <- mkReg(0);

   Integer delay = 1;

  assert property (r == fromInteger(-16) |=> ##[delay] res != oldres + 4 [*4]) else $finish(0);

  assert property (res == oldres + 4) $display("PASS: 1"); else $display("XFAIL: 1");

  assert property (res == 46 ##1 res == 50 ##1 res == 54 |=> res == 58 ##1 res == 62)
                  $display("PASS: 2"); else $display("FAIL: 2");

  assert property (res == 15 |=> res < 0 [*5])
                           $display("PASS: 3"); else $display("FAIL: 3");


  assert property (if (res < 0) r <= 3) else $display("FAIL:4");

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
