(* synthesize *)
module sysDontCareDynSelectStaticArrayReal ();

  Real arr[6] = { 1.1, 2.2, 3.3, 4.4, 5.5, 6.6 };
  // index can go out of bounds
  Reg#(Bit#(3)) idx <- mkReg(0);

  rule do_disp (idx < 6);
    Real x = arr[idx];
    $display(realToString(x));
    idx <= idx + 1;
  endrule

  rule do_finish (idx >= 6);
    $finish(0);
  endrule

endmodule

