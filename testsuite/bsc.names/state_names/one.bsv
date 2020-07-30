import Vector::*;

(* synthesize *)
module mkTest();

  Vector#(6, Reg#(Bool)) elements = replicate(?);
  for(Integer i = 0; i < 5; i = i + 1)
  begin
    elements[i] <- mkRegU();
  end
  elements[5] <- mkReg(False);

  rule r;
    for(Integer i = 0; i < 6; i = i + 1)
      $display("%b", elements[i]);
    $finish(0);
  endrule

endmodule: mkTest
