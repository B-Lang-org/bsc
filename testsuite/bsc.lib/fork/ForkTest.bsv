import Fork::*;

(* synthesize *)
module sysForkTest(Empty);

  Reg#(Bit#(32)) r();
  mkReg#(0) i_r(r);

  rule test (True);
    let lst = forkL(2, r + 1);
    $display("Forked %0d %0d", lst[0], lst[1]);
    $finish(0);
  endrule: test

endmodule: sysForkTest

