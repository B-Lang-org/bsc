import Vector::*;

(* synthesize *)
module mkTest();

  Vector#(6, Vector#(3, Reg#(Bool))) elements = replicate(replicate(?));

  for(Integer i = 0; i < 6; i = i + 1)
  begin
    for(Integer j = 0; j < 2; j = j + 1)
    begin
      elements[i][j] <- mkRegU();
    end
    elements[i][2] <- mkReg(False);
  end

  rule r;
    for(Integer i = 0; i < 6; i = i + 1)
      for(Integer j = 0; j < 3; j = j + 1)
        $display("%b", elements[i][j]);
    $finish(0);
  endrule

endmodule: mkTest
