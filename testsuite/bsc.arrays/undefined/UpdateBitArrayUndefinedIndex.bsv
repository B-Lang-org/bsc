(* synthesize *)
module sysUpdateBitArrayUndefinedIndex();

  Bit#(32) v = '1;

  v[?] = 0;

  rule test;
    $displayh(v);
  endrule
 
endmodule