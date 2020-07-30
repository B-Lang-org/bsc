import Vector::*;

(* synthesize *)
module sysVectorUninitErr7();
   
  Vector#(7, Bit#(32)) v;

  if (False) begin
     v = replicate(0);
  end
  
  rule test;
    $display(v[2]);
  endrule

endmodule
   
