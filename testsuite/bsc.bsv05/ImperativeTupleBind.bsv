module mkSub (Tuple3#(Bool, Integer, Bit#(8)));
  return tuple3(True,1,2);
endmodule

module mkTest ();
  Bool b;
  Integer i;
  Bit#(8) v;
  {b,i,v} <- mkSub;
endmodule

