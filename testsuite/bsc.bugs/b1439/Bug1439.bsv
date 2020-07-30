(* synthesize *)
module mkBug1439 ();

  Reg#(Bit#(12)) x <- mkReg(0);
  Reg#(Bit#(12)) y <- mkReg(1);

  let \x' = x + y;

  rule r (\x' == 1);
    $display("x+y: %0d", \x' );
    $finish(0);
  endrule

endmodule


    