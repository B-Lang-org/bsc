(* synthesize *)
module sysSelectUndefinedArray();
  
  UInt#(17) arr[4] = ?;

  Reg#(Bool) r <- mkReg(False);

  rule test;
    $display("%0d", arr[r ? 0 : 1]);
    r <= !r;
    if(r) $finish(0);
  endrule

endmodule
