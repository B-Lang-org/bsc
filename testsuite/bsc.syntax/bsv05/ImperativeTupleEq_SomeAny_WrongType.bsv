function Tuple3#(UInt#(5), Bit#(32), Bit#(8)) fn();
  return tuple3(7,8,9);
endfunction

module mkTest ();
  Bool b;
  Integer i;

  // the types of the first two are wrong
  {b, i, .*} = fn;
endmodule

