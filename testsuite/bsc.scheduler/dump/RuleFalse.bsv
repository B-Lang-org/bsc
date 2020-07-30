module sysRuleFalse(Empty);
  Reg#(Bit#(32)) r();
  mkReg#(0) i_r(r);

  rule never (False); 
   r <= r + 17;
  endrule: never

  rule tricky ((r > 6) && (r <= 5));
   r <= 0;
  endrule: tricky

  rule count (True);
   r <= r + 1;
  endrule: count
endmodule: sysRuleFalse
