typeclass TC#(type c);
   function c#(n) fn(c#(n) x);
endtypeclass

instance TC#(Bit);
   function fn(x) = x + 1;
endinstance

(* synthesize *)
module sysClassKind1();
  Reg#(Bit#(8)) rg <- mkReg(0);
  rule r;
    Bit#(8) v = fn(rg);
    $display(v);
    $finish(0);
  endrule
endmodule

