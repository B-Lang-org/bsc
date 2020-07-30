(* synthesize *)
module sysDontCareRealPrim ();
  Reg#(Bool) rg <- mkRegU;
  rule test;
    Real a = ?;
    rg <= (a > 0);
  endrule
endmodule

