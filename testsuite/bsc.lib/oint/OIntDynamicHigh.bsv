import OInt::*;

(* synthesize *)
module sysOIntDynamic(Empty);

  Reg#(Bool) b <- mkReg(False);

  OInt#(8) o = b ? 4 : 22;
  
  rule flip;
    b <= !b;
  endrule

  rule test;
    $display("o: %b", o);
    if(o == 4) $finish(0);
  endrule

endmodule
    