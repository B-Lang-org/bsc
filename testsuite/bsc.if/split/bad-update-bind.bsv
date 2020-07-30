typedef struct { Bit#(64) ii ; Bool bb; } Mystruct;

(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        Mystruct mm=?;
        (*split*)
        mm.ii <- $time;

        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
