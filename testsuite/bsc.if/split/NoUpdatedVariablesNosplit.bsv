(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        int x=10;

        (* nosplit *)
        if (myregister)
        $display("123");
        else
        action
          $display("999");
          x=14;
        endaction
  endrule
endmodule
