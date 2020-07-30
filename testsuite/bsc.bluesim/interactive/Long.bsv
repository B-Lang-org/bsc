(* synthesize *)
module mkLong();

  Reg#(UInt#(32)) count <- mkReg(0);

  rule incr;
    count <= count + 1;
  endrule

  rule print ((count % 100000000) == 99999999);
    $display("count = %d", count);
  endrule

  rule done (count > 300000000);
    $finish(0);
  endrule

endmodule