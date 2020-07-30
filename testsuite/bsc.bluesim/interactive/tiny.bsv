(* synthesize *)
module mkTest();

  Reg#(UInt#(16)) count <- mkReg(0);

  rule incr (count < 100);
    count <= count + 1;
    $display("%t: %d", $time(), count);
  endrule: incr

  rule done (count == 100);
    $finish(0);
  endrule: done

endmodule
