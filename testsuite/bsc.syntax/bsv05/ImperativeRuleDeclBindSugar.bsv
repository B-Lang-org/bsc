module mkFoo();
  rule bogus;
    Bool x <- actionvalue return(True); endactionvalue;
  endrule
endmodule
