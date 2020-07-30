import Vector::*;

(* synthesize *)
module sysVectorUninitErr6();
   
  Vector#(7, Bit#(32)) v;

  v[1] = 0;
  v[3] = 0;
  v[4] = 0;
  
  rule test;
    $display(v);
  endrule

endmodule
   
