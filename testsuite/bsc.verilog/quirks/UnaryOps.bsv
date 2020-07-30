// test quirk handling in Verilog generation for unary ops (~,!,-)
// no unary ops on non-primary expressions
(* synthesize *)
module sysUnaryOps(Empty);

  Reg#(Bit#(19)) r();
  mkReg#(12) the_r(r);

  Reg#(Bit#(19)) s();
  mkReg#(17) the_s(s);

  Reg#(Bit#(19)) t();
  mkReg#(33) the_t(t);

  Reg#(Bool) a();
  mkReg#(True) the_a(a);

  Reg#(Bool) b();
  mkReg#(False) the_b(b);
   
   Reg#(Bool) c <- mkReg(False);
  rule bogus;
    r <= -(-r);
    s <= ~(~s);
    t <= -(r + s);
    a <= !(a == (a || b));
     b <= !(!b);
     c <= unpack(~ (pack(!c))) ;
  endrule

endmodule

  
