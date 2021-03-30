module mkFoo();
  rule bogus;
    Bool x;
    x <- actionvalue return(True); endactionvalue;
  endrule
endmodule
