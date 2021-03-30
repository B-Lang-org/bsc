module mkFoo();
  rule bogus;
    function Bool f(Bool x);
      f = x;
    endfunction
  endrule
endmodule
