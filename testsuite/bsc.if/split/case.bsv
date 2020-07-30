(* synthesize *)
module sysx () ;
  Reg#(int) myregister <- mkRegU();
  rule foobar;
        (*split*)
        case (myregister)
          1 : $display("123");
          2 : $display("999");
        endcase
  endrule
endmodule
