function Bit#(8) fn1();
  return 17;
endfunction

function Tuple3#(UInt#(5), Bit#(32), Bit#(8)) fn2();
  return tuple3(7,8,9);
endfunction

module mkTest ();
  Bool b;
  Integer i;
  let v = fn1;

  // the types of the first two are wrong
  {b,i,v} = fn2;
endmodule

