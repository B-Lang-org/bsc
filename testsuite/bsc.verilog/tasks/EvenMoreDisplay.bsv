export sysEvenMoreDisplay;

module sysEvenMoreDisplay(Empty);
  Reg#(UInt#(4)) counter <- mkReg(0);
  Reg#(Int#(16))  r1 <- mkReg(-9238);
  Reg#(Int#(78))  r2 <- mkReg(48446744073709551677);

  rule display (counter <= 10);
    $display("r1        = ", r1);
    $displayb("in binary = ", r1);
    $displayo("in octal  = ", r1);
    $displayh("in hex    = ", r1);
    $display("r2        = ", r2);
    $displayb("in binary = ", r2);
    $displayo("in octal  = ", r2);
    $displayh("in hex    = ", r2);
    r1 <= r1 + signExtend(unpack(pack(r2)[11:0]));
    r2 <= r2 * signExtend(r1);
    counter <= counter + 1;
  endrule: display
 
  rule done (counter > 10);
    $finish(0);
  endrule: done

endmodule: sysEvenMoreDisplay
