module mkFoo();
  rule bogus;
    bit x;
    action
      bit y;
      y = 1;
      x = y;
    endaction
  endrule
endmodule
