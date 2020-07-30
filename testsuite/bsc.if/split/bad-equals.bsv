(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  int j=20;
  rule foobar;
        int i=10;
        (*split*)
        i=j;
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
