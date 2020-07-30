import Vector :: *;

(* synthesize *)
module sysUpdateVectorUndefinedIndex();

  Vector#(4, int) vec = replicate(17);

  vec[?] = 0;

  rule test;
    $displayh(vec);
  endrule
 
endmodule