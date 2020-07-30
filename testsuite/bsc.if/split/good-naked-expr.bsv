(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();

  rule foobar;
      Action a=action
        if (myregister)
        $display("123");
        else
        $display("999");
      endaction;
      (*split*)
      a;
  endrule
endmodule
