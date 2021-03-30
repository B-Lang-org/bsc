module mkTest ();
  Bool b;
  Integer i;
  Bit#(8) v;
  // False is the wrong type here
  {b,i,v} = tuple3(True,1,False);
endmodule

