(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Tuple2#(Bit#(32), Bool) data;
  data=tuple2(10,True);
  rule foobar;
        (*split*)
        match {.in, .start} = data;
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
