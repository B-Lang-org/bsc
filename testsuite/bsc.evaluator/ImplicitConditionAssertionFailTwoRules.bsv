import FIFO::*;

(* synthesize *)
module sysImplicitConditionAssertionFailTwoRules();

  FIFO#(UInt#(93)) f <- mkFIFO;

  Reg#(UInt#(93)) count <- mkReg(9700);

  (* no_implicit_conditions *)
  rule do_enq;
    f.enq(count);
    count <= count + 1;
  endrule

  (* no_implicit_conditions *)
  rule do_deq;
    f.deq;
    $finish(0);
  endrule

endmodule
