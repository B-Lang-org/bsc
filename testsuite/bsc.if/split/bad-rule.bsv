(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  (*split*)
  rule foobar;
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
