(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(Bool) myregister2 <- mkRegU();
  Reg#(Bool) myregister3 <- mkRegU();
  rule foobar;
        (* split *)
        if (myregister)
                action
                        $display("a");
                        if (myregister2)
                                $display("b");
                        else
                                $display("c");
                        $display("d");
                endaction
        else
                $display("e");

        if (myregister3)
                $display("f");
        else
                $display("g");
  endrule
endmodule
