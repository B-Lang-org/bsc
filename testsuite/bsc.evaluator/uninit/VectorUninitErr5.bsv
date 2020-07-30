import Vector::*;

(* synthesize *)
module sysVectorUninitErr4();
   
  Vector#(7, Bit#(32)) v;

  if (False) begin
     v[1] = 0;
  end
  
  rule test;
    for (Integer i = 0; i < 6; i = i + 1)    
      $display(v[i]);
  endrule

endmodule
   
