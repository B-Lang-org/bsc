import Vector::*;

(* synthesize *)
module sysVectorUninitErr4();
   
  Vector#(7, Bit#(32)) v;

  if (False) begin
     v[1] = 0;
  end
  
  rule test;
    $display(v);
  endrule

endmodule
   
