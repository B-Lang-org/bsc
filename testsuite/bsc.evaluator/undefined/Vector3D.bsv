import Vector::*;

(* synthesize *)
module sysVector3D(Empty);
  Vector#(4, Vector#(4, Vector#(4, UInt#(8)))) vs = ?;
  for(Integer i = 0; i < 4; i = i + 1)
    for(Integer j = 0; j < 4; j = j + 1)
      for(Integer k = 0; k < 4; k = k + 1)
        vs[i][j][k] = fromInteger(i + (j * k));

  Reg#(UInt#(17)) count <- mkReg(0); 

  rule tick;
    count <= count + 1;
    if(count == 1) $finish(0);
  endrule

  rule init_display(count == 0);
    for(Integer i = 0; i < 4; i = i + 1)
      for(Integer j = 0; j < 4; j = j + 1)
        for (Integer k = 0; k < 4; k = k + 1) begin
          $display("vs[%0d][%0d][%0d] = %0d", i, j, k, vs[i][j][k]);
          $display("i + (j * k) = %0d", i + (j * k));
        end
  endrule

endmodule
   