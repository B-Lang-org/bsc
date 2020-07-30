(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        (* split *)
        begin
        let x=10;
        if (myregister)
        action
                $display(x);
        endaction
        else
        $display("999");
        end
  endrule
endmodule
