typeclass TC#(type c);
   function c#(n) fn(c#(n) x);
   // attempt to fix the kind with a dummy function
   function Bit#(n) dummy(c#(n) x);
endtypeclass

instance TC#(Bit);
   function fn(x) = x + 1;
   function dummy = ?;
endinstance

(* synthesize *)
module sysClassKind2();
  Reg#(Bit#(8)) rg <- mkReg(0);
  rule r;
    Bit#(8) v = fn(rg);
    $display(v);
    $finish(0);
  endrule
endmodule

