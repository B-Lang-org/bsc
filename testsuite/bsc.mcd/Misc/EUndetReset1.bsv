(* synthesize *)
module sysEUndetReset1(Empty);

  Reg#(Bool) r();
  mkReg#(False) the_r(r, reset_by ?);
endmodule

