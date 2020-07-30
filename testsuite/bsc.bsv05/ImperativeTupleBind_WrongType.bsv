module mkSub (Tuple3#(Bool, Integer, Bool));
  return tuple3(True,1,False);
endmodule

module mkTest ();
  Bool b;
  Integer i;
  Bit#(8) v;
  // Third element has the wrong type here
  {b,i,v} <- mkSub;
endmodule

