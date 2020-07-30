(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(Bool) myregister2 <- mkRegU();
  rule foobar;
        (* nosplit *)
        if (myregister)
                action
                        $display("a");
                        (* split *)
                        if (myregister2)
                                $display("b");
                        else
                                $display("c");
                        $display("d");
                endaction
        else
                $display("999");

  endrule
endmodule
