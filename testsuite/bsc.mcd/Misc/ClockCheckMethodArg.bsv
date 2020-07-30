(* synthesize *)
module sysClockCheckMethodArg#(Clock c)(Empty);

Reg#(Bit#(8)) r <- mkReg(0);
Reg#(Bit#(8)) s();
mkRegU the_s(s, clocked_by(c));

rule test;
  r <= s;
  $finish(0);
endrule

endmodule

