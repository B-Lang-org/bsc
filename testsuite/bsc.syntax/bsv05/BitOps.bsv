(* synthesize *)
module sysBitOps();
  Reg #(Bool) start();
  mkReg #(True) start_instance(start);

  rule runTest (start);
    start <= False;
    for (bit[3:0] i = 'b0000; i < 'b1000; i = i + 1) begin
      bit[2:0] x = i[2:0];
      $display("&  %b = %b", x, & x);
      $display("|  %b = %b", x, | x);
      $display("^  %b = %b", x, ^ x);
      $display("~& %b = %b", x, ~& x);
      $display("~| %b = %b", x, ~| x);
      $display("~^ %b = %b", x, ~^ x);
      $display("^~ %b = %b", x, ^~ x);
    end
    for (bit[2:0] i = 'b000; i < 'b100; i = i + 1) begin
      bit[1:0] x = i[1:0];
      for (bit[2:0] j = 'b000; j < 'b100; j = j + 1) begin
        bit[1:0] y = j[1:0];
        $display("%b &  %b = %b", x, y, x & y);
        $display("%b |  %b = %b", x, y, x | y);
        $display("%b ^  %b = %b", x, y, x ^ y);
        $display("%b ~^ %b = %b", x, y, x ~^ y);
        $display("%b ^~ %b = %b", x, y, x ^~ y);
      end
    end
  endrule: runTest
endmodule: sysBitOps
