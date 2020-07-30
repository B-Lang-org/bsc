module mkSub (Bit#(8));
  return 12;
endmodule

module mkTest();
  let x = True;
  x <- mkSub;
endmodule

