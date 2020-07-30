import Vector :: *;

(* synthesize *)
module sysUpdateUndefinedVector();

  Vector#(4, int) vec = ?;
  vec[0] = 17;

  rule test;
    $displayh(vec);
  endrule
 
endmodule