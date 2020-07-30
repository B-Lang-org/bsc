function Bit#(8) fn();
  return 12;
endfunction

module mkTest();
  let x = True;
  x = fn;
endmodule

