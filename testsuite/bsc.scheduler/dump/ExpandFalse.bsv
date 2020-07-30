
// test that we don't warn about false rules that result from if splitting
module sysExpandFalse(Empty);
  Reg#(Bit#(32)) r(); 
  mkReg#(0) i_r(r);

  rule go (True);
    if(r == 0) 
    action
      r <= r + 1;
      if(r == 5) 
        r <= 7;
    endaction
    else if(r == 9) 
      r <= 12;
    if (r == 19) 
      r <= 21;
  
  endrule: go
endmodule: sysExpandFalse
