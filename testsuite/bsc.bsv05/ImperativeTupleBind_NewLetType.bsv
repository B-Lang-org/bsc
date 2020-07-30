function Bool fn();
  return True;
endfunction

module mkSub (Tuple2#(Integer, Bit#(8)));
  return tuple2(17,42);
endmodule

module mkTest();
  Integer x;
  let y = fn; // type is Bool

  // type of the second element is Bit#(8) here
  { x, y } <- mkSub;
endmodule

