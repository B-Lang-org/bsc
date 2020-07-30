import ListN::*;

(* synthesize *)
module sysListNReg3D(Empty);
  ListN#(4, ListN#(4, ListN#(4, Reg#(UInt#(8))))) lns = ?;

  for(Integer i = 0; i < 4; i = i + 1)
    for(Integer j = 0; j < 4; j = j + 1)
      for(Integer k = 0; k < 4; k = k + 1)
        lns[i][j][k] <- mkReg(0);

  Reg#(UInt#(8)) i <- mkReg(0);
  Reg#(UInt#(8)) j <- mkReg(0);
  Reg#(UInt#(8)) k <- mkReg(0);

  rule display_data(k == 4);
    for(Integer i0 = 0; i0 < 4; i0 = i0 + 1)
      for(Integer j0 = 0; j0 < 4; j0 = j0 + 1)
        for (Integer k0 = 0; k0 < 4; k0 = k0 + 1) begin
          $display("lns[%0d][%0d][%0d] = %0d", i0, j0, k0, lns[i0][j0][k0]);
          $display("i + (j * k) = %0d", i0 + (j0 * k0));
        end
    $finish(0);
  endrule

  rule display;
    $display("Current field", lns[i][j][k]);
  endrule

  rule write(i < 4 && j < 4 && k < 4);
    $display("Writing lns[%0d][%0d][%0d]", i, j, k);
    lns[i][j][k] <= i + (j * k);
  endrule

  rule tick(k < 4);
    if (i + 1 == 4) begin
      i <= 0;
      if (j + 1 == 4) begin
        j <= 0;
        k <= k + 1;
      end
      else j <= j + 1;
    end
    else i <= i + 1;
  endrule

endmodule
