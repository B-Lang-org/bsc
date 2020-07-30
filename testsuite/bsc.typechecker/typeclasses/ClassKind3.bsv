import ClassKind3Sub::*;

instance TC#(Bit);
   function fn(x) = x + 1;
endinstance

(* synthesize *)
module sysClassKind3();
  Reg#(Bit#(8)) rg <- mkReg(0);
  rule r;
    Bit#(8) v = fn(rg);
    $display(v);
    $finish(0);
  endrule
endmodule

