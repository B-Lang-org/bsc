module mkFoo();
  rule bogus(match .x = ctr[1] &&& x==0);
  endrule
endmodule
