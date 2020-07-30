import Vector :: *;

(* synthesize *)
module sysSelectUndefinedVector();
  
  Vector#(4, Bit#(8)) vec = ?;

  Reg#(Bool) r <- mkReg(False);

  rule test;
    $display("%0d", vec[r ? 0 : 1]);
    r <= !r;
    if(r) $finish(0);
  endrule

endmodule
