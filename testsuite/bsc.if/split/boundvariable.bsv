(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        (* split *)
        let x=10;
        if (myregister)
        action
                $display(x);
        endaction
        else
        $display("999");

  endrule
endmodule
