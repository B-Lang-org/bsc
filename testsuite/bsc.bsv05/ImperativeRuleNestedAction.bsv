module mkFoo();
  rule bogus;
    bit x;
    begin
      bit z;
      action
        bit y;
        begin
          y = 1;
        end
        x = y;
      endaction
      z = 1;
    end
    x = x;
  endrule
endmodule
