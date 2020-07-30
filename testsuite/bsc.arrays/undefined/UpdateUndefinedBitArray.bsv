(* synthesize *)
module sysUpdateUndefinedBitArray();

  Bit#(32) v = ?;
  v[0] = 1;
  v[1] = 1;
  v[2] = 1;
  v[3] = 1;

  rule test;
    $displayh(v);
  endrule
 
endmodule