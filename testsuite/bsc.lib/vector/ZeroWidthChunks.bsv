import Vector::*;

// toChunks and fromChunks of a zero-width value: the chunk vector is
// empty, and the bit extraction that trims the chunk padding has no
// bits to extract

(* synthesize *)
module sysZeroWidthChunks();

  rule test;
    Bit#(0) x = 0;
    Vector#(0, Bit#(8)) c = toChunks(x);
    $display("%0d", pack(c));
    Bit#(0) y = fromChunks(c);
    $display("%0d", pack(y));
    $display("%0d", pack(y == x));
    $finish(0);
  endrule

endmodule
