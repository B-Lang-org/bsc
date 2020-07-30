import FIFO::*;

(* options="-steps-warn-interval 1000" *)
(* synthesize *)
module sysStepsIntervalError();

  FIFO#(Int#(23)) f <- mkFIFO;

  (* no_implicit_conditions *)
  rule do_enq;
    f.enq(0);
  endrule

  Integer j = 0;
  for(Integer i = 0; i < 1000; i = primSeq(j, i + 1))
  begin
    j = j + i;
  end

  rule test;
    $display(j);
    $finish(0);
  endrule

endmodule

