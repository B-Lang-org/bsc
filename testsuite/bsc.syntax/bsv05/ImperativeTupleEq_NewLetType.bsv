function Bool fn1();
  return True;
endfunction

function Tuple2#(Integer, Bit#(8)) fn2();
  return tuple2(17,42);
endfunction

module mkTest();
  Integer x;
  let y = fn1; // type is Bool

  // type of the second element is Bit#(8) here
  { x, y } = fn2;
endmodule

