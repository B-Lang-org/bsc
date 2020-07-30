(* synthesize *)
module sysEUndetClock1(Empty);

  Reg#(Bool) r();
  mkRegU the_r(r, clocked_by ?);
endmodule

