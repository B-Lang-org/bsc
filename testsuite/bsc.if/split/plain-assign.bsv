(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(int) i <- mkRegU();
  rule foobar;
        (* split *)
        if (myregister)
                i <= 10;
        else
                i <= 20;
  endrule
endmodule
