(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(int) i <- mkRegU();
  rule foobar;
        (* split *)
        if (myregister)
        action
        let temp = 
                action
                i <= 10;
                endaction;
        temp;
        endaction
        else
        action
        let temp = 
                action
                i <= 20;
                endaction;
        temp;
        endaction
  endrule
endmodule
