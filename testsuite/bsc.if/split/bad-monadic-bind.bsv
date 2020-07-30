(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        Bit#(64) ii;
        (* split *)
        ii <- $time;

        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
