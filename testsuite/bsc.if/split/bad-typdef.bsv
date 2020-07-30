(* split *)
typedef bit[99:0] Byte99;

(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  Reg#(Byte99) x <- mkRegU();
  rule foobar;
        if (myregister)
        $display(x);
        else
        $display("999");

  endrule
endmodule
