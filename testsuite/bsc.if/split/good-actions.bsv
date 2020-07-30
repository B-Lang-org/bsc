import Vector :: *;
(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(int) reg2 <- mkRegU();
  Vector#(64,Reg#(UInt#(6))) vr <- replicateM(mkRegU());
  Reg#(UInt#(6)) i <- mkRegU();

  rule foobar;
        //both these actually do not split to anything useful
        (* split *)
        reg2 <= myregister?10:20;
        (*split*)
        vr[10]<=10;
  endrule
endmodule
