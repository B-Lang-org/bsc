import Vector :: *;
(* synthesize *)
module sysx () ;
  Vector#(64,Reg#(UInt#(6))) vr <- replicateM(mkRegU());
  Reg#(UInt#(6)) i <- mkRegU();
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        (*split*)
        // should be split into 64 different rules
        vr[i] <= i;

  endrule
endmodule
