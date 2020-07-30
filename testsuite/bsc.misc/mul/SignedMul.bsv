import Vector::*;

(* synthesize *)
module sysSignedMul();

  Reg#(Int#(3)) i <- mkReg(-4);
  Reg#(Int#(7)) j <- mkReg(-64);

  Vector#(8, Vector#(128, Int#(10))) answers = ?;

  for(Integer k = -4; k < 4; k = k + 1)
    for(Integer l = - 64; l < 64; l = l + 1)
      answers[k+4][l+64] = fromInteger(k*l);

  Int#(10) result = signedMul(i,j);

  rule test;
    $display("i: %0d j: %0d i*j: %0d", i, j, result);

    Int#(4) i_index = signExtend(i) + 4;
    Int#(8) j_index = signExtend(j) + 64;
    if(result != answers[i_index][j_index]) begin
      $display("Test failed");
      $finish(0);
    end

    if(i == 3 && j == 63) begin
      $display("Test passed");
      $finish(0);
    end

    i <= i + 1;
    if (i == 3) j <= j + 1;
  endrule

endmodule
