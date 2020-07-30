typedef struct { int ii ; Bool bb; } Mystruct;

(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  rule foobar;
        Mystruct mm;
        (*split*)
        mm.ii=20;
        if (myregister)
        $display("123");
        else
        $display("999");

  endrule
endmodule
