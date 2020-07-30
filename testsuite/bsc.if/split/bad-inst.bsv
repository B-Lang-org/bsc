(* synthesize *)
module sysx () ;
  Reg#(Bool) myregister <- mkRegU();
  (*split*)
  Reg#(Bool) reg2();
  mkReg#(False) i_reg(reg2);

  rule foobar;
        if (myregister)
        $display("123");
        else
        $display("999");
  endrule
endmodule
