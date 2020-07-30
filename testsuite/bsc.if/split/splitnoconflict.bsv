(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        (* split, split *)
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
