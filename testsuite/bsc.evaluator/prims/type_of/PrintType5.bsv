(* synthesize *)
module sysPrintType5();
   
  Bit#(5) a = 0;
  let b = zeroExtend(a);
  messageM(printType(typeOf(b)));

endmodule

