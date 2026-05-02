(* synthesize *)
module sysStringLT();

  Reg#(Bit#(2)) c <- mkReg(0);

  String x = (c[0] == 1) ? "A" : "B";
  String y = (c[1] == 1) ? "A" : "B";

  String z = (c[0] == 1) ? "" : "X";
  String w = (c[1] == 1) ? "" : "X";

  rule test;
    $display("Test %b", c);

    if (x < y) $display("x is less than y");
    else $display("x is not less than y");

    if (z < w) $display("z is less than w");
    else $display("z is not less than w");

    if (x <= y) $display("x is less than or equal to y");
    else $display("x is not less than or equal to y");

    if (z <= w) $display("z is less than or equal to w");
    else $display("z is not less than or equal to w");

    if (x > y) $display("x is greater than y");
    else $display("x is not greater than y");

    if (z > w) $display("z is greater than w");
    else $display("z is not greater than w");

    if (x >= y) $display("x is greater than or equal to y");
    else $display("x is not greater than or equal to y");

    if (z >= w) $display("z is greater than or equal to w");
    else $display("z is not greater than or equal to w");

    c <= c + 1;
    if (c == 3) $finish(0);
  endrule

endmodule
