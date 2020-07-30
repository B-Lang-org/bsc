import OInt::*;

(* synthesize *)
module sysOIntDynamicLow(Empty);

  Reg#(Bool) b <- mkReg(False);

  OInt#(8) o = b ? 4 : -1;
  
  rule flip;
    b <= !b;
  endrule

  rule test;
    $display("o: %b", o);
    if(o == 4) $finish(0);
  endrule

endmodule
    