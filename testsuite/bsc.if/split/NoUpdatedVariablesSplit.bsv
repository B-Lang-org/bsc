(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        int y=10;

        (* split *)
        if (myregister)
        $display("123");
        else
        action
          $display("999");
          y=14;
        endaction
  endrule
endmodule
