module m();
  Reg#(Maybe#(Bool)) mb();
  mkReg#(Invalid) the_mb(mb);
  int x = 5;
  rule foo(mb matches tagged Valid .x);
  endrule
endmodule
