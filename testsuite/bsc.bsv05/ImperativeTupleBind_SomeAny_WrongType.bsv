module mkSub (Tuple3#(UInt#(5), Bit#(32), Bit#(8)));
  return tuple3(7,8,9);
endmodule

module mkTest ();
  Bool b;
  Integer i;

  // the types of the first two are wrong
  {b, i, .*} <- mkSub;
endmodule

