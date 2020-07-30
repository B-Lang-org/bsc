(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        Bit#(64) ii;

        (* split *)
        if (myregister)
        $display("123");
        else
        action
          $display("999");
          ii <- $time;
        endaction
  endrule
endmodule
