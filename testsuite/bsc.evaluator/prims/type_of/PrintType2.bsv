(* synthesize *)
module sysPrintType2();

  Bit#(17) b = 0;
  messageM(printType(typeOf(b))); 

endmodule

