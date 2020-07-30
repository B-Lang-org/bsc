module tbParamSize(CLK,
		    RST_N);
  input  CLK;
  input  RST_N;

  // use an unsized parameter value (which will default to 32-bit)
  mkParamSize_Sub #(.b(1)) i(.CLK(CLK), .RST_N(RST_N));
endmodule

