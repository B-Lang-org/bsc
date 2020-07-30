(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(Bool) myregister2 <- mkRegU();
  Reg#(Bool) myregister3 <- mkRegU();
  rule foobar;
        (* split *)
        //exponential number of rules
        action
        if (myregister)
                $display("a");
        else
                $display("b");

        if (myregister2)
                $display("c");
        else
                $display("d");

        if (myregister3)
                $display("e");
        else
                $display("f");
        endaction
  endrule
endmodule
