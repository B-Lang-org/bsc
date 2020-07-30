(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        (* nosplit *)
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
