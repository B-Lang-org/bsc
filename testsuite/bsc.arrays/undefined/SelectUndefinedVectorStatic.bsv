import Vector :: *;

(* synthesize *)
module sysSelectUndefinedVectorStatic();
  
  Vector#(4, Bit#(8)) vec = ?;

  rule test;
    $display("%0d", vec[1]);
    $finish(0);
  endrule

endmodule
