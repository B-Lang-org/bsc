(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  (*split*)
  int i;
  rule foobar;
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
